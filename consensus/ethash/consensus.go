// Copyright 2017 The go-ethereum Authors
// This file is part of the go-ethereum library.
//
// The go-ethereum library is free software: you can redistribute it and/or modify
// it under the terms of the GNU Lesser General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.
//
// The go-ethereum library is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
// GNU Lesser General Public License for more details.
//
// You should have received a copy of the GNU Lesser General Public License
// along with the go-ethereum library. If not, see <http://www.gnu.org/licenses/>.

package ethash

import (
    "errors"
    "fmt"
    "math/big"
    "time"

    mapset "github.com/deckarep/golang-set/v2"
    "github.com/ethereum/go-ethereum/common"
    "github.com/ethereum/go-ethereum/consensus"
    "github.com/ethereum/go-ethereum/consensus/misc"
    "github.com/ethereum/go-ethereum/consensus/misc/eip1559"
    "github.com/ethereum/go-ethereum/core/state"
    "github.com/ethereum/go-ethereum/core/tracing"
    "github.com/ethereum/go-ethereum/core/types"
    "github.com/ethereum/go-ethereum/core/vm"
    "github.com/ethereum/go-ethereum/params"
    "github.com/ethereum/go-ethereum/rlp"
    "github.com/ethereum/go-ethereum/trie"
    "github.com/holiman/uint256"
    "golang.org/x/crypto/sha3"
)

// Ethash proof-of-work protocol constants.
var (
    FrontierBlockReward           = uint256.NewInt(5e+18) // Block reward in wei for successfully mining a block
    ByzantiumBlockReward          = uint256.NewInt(3e+18) // Block reward in wei for successfully mining a block upward from Byzantium
    ConstantinopleBlockReward     = uint256.NewInt(2e+18) // Block reward in wei for successfully mining a block upward from Constantinople
    DeennixBlockReward            = uint256.NewInt(5e+18) // Block reward for Deennix network (5 ETH in wei, adjustable)
    maxUncles                     = 2                     // Maximum number of uncles allowed in a single block
    allowedFutureBlockTimeSeconds = int64(15)             // Max seconds from current time allowed for blocks, before they're considered future blocks

    // Difficulty adjustment calculators for various forks
    calcDifficultyEip5133        = makeDifficultyCalculator(big.NewInt(11_400_000))
    calcDifficultyEip4345        = makeDifficultyCalculator(big.NewInt(10_700_000))
    calcDifficultyEip3554        = makeDifficultyCalculator(big.NewInt(9700000))
    calcDifficultyEip2384        = makeDifficultyCalculator(big.NewInt(9000000))
    calcDifficultyConstantinople = makeDifficultyCalculator(big.NewInt(5000000))
    calcDifficultyByzantium      = makeDifficultyCalculator(big.NewInt(3000000))
)

// Various error messages to mark blocks invalid.
var (
    errOlderBlockTime  = errors.New("timestamp older than parent")
    errTooManyUncles   = errors.New("too many uncles")
    errDuplicateUncle  = errors.New("duplicate uncle")
    errUncleIsAncestor = errors.New("uncle is ancestor")
    errDanglingUncle   = errors.New("uncle's parent is not ancestor")
)

// Author implements consensus.Engine, returning the header's coinbase as the
// proof-of-work verified author of the block.
func (ethash *Ethash) Author(header *types.Header) (common.Address, error) {
    return header.Coinbase, nil
}

// VerifyHeader checks whether a header conforms to the consensus rules of the
// stock Ethereum ethash engine.
func (ethash *Ethash) VerifyHeader(chain consensus.ChainHeaderReader, header *types.Header) error {
    // Short circuit if the header is known, or its parent not
    number := header.Number.Uint64()
    if chain.GetHeader(header.Hash(), number) != nil {
        return nil
    }
    parent := chain.GetHeader(header.ParentHash, number-1)
    if parent == nil {
        return consensus.ErrUnknownAncestor
    }
    // Sanity checks passed, do a proper verification
    return ethash.verifyHeader(chain, header, parent, false, time.Now().Unix())
}

// VerifyHeaders is similar to VerifyHeader, but verifies a batch of headers
// concurrently. The method returns a quit channel to abort the operations and
// a results channel to retrieve the async verifications.
func (ethash *Ethash) VerifyHeaders(chain consensus.ChainHeaderReader, headers []*types.Header) (chan<- struct{}, <-chan error) {
    if ethash.fakeFull || len(headers) == 0 {
        abort, results := make(chan struct{}), make(chan error, len(headers))
        for i := 0; i < len(headers); i++ {
            results <- nil
        }
        return abort, results
    }
    abort := make(chan struct{})
    results := make(chan error, len(headers))
    unixNow := time.Now().Unix()

    go func() {
        for i, header := range headers {
            var parent *types.Header
            if i == 0 {
                parent = chain.GetHeader(headers[0].ParentHash, headers[0].Number.Uint64()-1)
            } else if headers[i-1].Hash() == headers[i].ParentHash {
                parent = headers[i-1]
            }
            var err error
            if parent == nil {
                err = consensus.ErrUnknownAncestor
            } else {
                err = ethash.verifyHeader(chain, header, parent, false, unixNow)
            }
            select {
            case <-abort:
                return
            case results <- err:
            }
        }
    }()
    return abort, results
}

// VerifyUncles verifies that the given block's uncles conform to the consensus
// rules of the stock Ethereum ethash engine.
func (ethash *Ethash) VerifyUncles(chain consensus.ChainReader, block *types.Block) error {
    if ethash.fakeFull {
        return nil
    }
    if len(block.Uncles()) > maxUncles {
        return errTooManyUncles
    }
    if len(block.Uncles()) == 0 {
        return nil
    }
    uncles, ancestors := mapset.NewSet[common.Hash](), make(map[common.Hash]*types.Header)

    number, parent := block.NumberU64()-1, block.ParentHash()
    for i := 0; i < 7; i++ {
        ancestorHeader := chain.GetHeader(parent, number)
        if ancestorHeader == nil {
            break
        }
        ancestors[parent] = ancestorHeader
        if ancestorHeader.UncleHash != types.EmptyUncleHash {
            ancestor := chain.GetBlock(parent, number)
            if ancestor == nil {
                break
            }
            for _, uncle := range ancestor.Uncles() {
                uncles.Add(uncle.Hash())
            }
        }
        parent, number = ancestorHeader.ParentHash, number-1
    }
    ancestors[block.Hash()] = block.Header()
    uncles.Add(block.Hash())

    for _, uncle := range block.Uncles() {
        hash := uncle.Hash()
        if uncles.Contains(hash) {
            return errDuplicateUncle
        }
        uncles.Add(hash)
        if ancestors[hash] != nil {
            return errUncleIsAncestor
        }
        if ancestors[uncle.ParentHash] == nil || uncle.ParentHash == block.ParentHash() {
            return errDanglingUncle
        }
        if err := ethash.verifyHeader(chain, uncle, ancestors[uncle.ParentHash], true, time.Now().Unix()); err != nil {
            return err
        }
    }
    return nil
}

// verifyHeader checks whether a header conforms to the consensus rules of the
// stock Ethereum ethash engine.
func (ethash *Ethash) verifyHeader(chain consensus.ChainHeaderReader, header, parent *types.Header, uncle bool, unixNow int64) error {
    if uint64(len(header.Extra)) > params.MaximumExtraDataSize {
        return fmt.Errorf("extra-data too long: %d > %d", len(header.Extra), params.MaximumExtraDataSize)
    }
    if !uncle {
        if header.Time > uint64(unixNow+allowedFutureBlockTimeSeconds) {
            return consensus.ErrFutureBlock
        }
    }
    if header.Time <= parent.Time {
        return errOlderBlockTime
    }
    expected := ethash.CalcDifficulty(chain, header.Time, parent)
    if expected.Cmp(header.Difficulty) != 0 {
        return fmt.Errorf("invalid difficulty: have %v, want %v", header.Difficulty, expected)
    }
    if header.GasLimit > params.MaxGasLimit {
        return fmt.Errorf("invalid gasLimit: have %v, max %v", header.GasLimit, params.MaxGasLimit)
    }
    if header.GasUsed > header.GasLimit {
        return fmt.Errorf("invalid gasUsed: have %d, gasLimit %d", header.GasUsed, header.GasLimit)
    }
    if !chain.Config().IsLondon(header.Number) {
        if header.BaseFee != nil {
            return fmt.Errorf("invalid baseFee before fork: have %d, expected 'nil'", header.BaseFee)
        }
        if err := misc.VerifyGaslimit(parent.GasLimit, header.GasLimit); err != nil {
            return err
        }
    } else if err := eip1559.VerifyEIP1559Header(chain.Config(), parent, header); err != nil {
        return err
    }
    if diff := new(big.Int).Sub(header.Number, parent.Number); diff.Cmp(big.NewInt(1)) != 0 {
        return consensus.ErrInvalidNumber
    }
    if chain.Config().IsShanghai(header.Number, header.Time) {
        return errors.New("ethash does not support shanghai fork")
    }
    if header.WithdrawalsHash != nil {
        return fmt.Errorf("invalid withdrawalsHash: have %x, expected nil", header.WithdrawalsHash)
    }
    if chain.Config().IsCancun(header.Number, header.Time) {
        return errors.New("ethash does not support cancun fork")
    }
    switch {
    case header.ExcessBlobGas != nil:
        return fmt.Errorf("invalid excessBlobGas: have %d, expected nil", header.ExcessBlobGas)
    case header.BlobGasUsed != nil:
        return fmt.Errorf("invalid blobGasUsed: have %d, expected nil", header.BlobGasUsed)
    case header.ParentBeaconRoot != nil:
        return fmt.Errorf("invalid parentBeaconRoot, have %#x, expected nil", header.ParentBeaconRoot)
    }
    if ethash.fakeDelay != nil {
        time.Sleep(*ethash.fakeDelay)
    }
    if ethash.fakeFail != nil && *ethash.fakeFail == header.Number.Uint64() {
        return errors.New("invalid tester pow")
    }
    if err := misc.VerifyDAOHeaderExtraData(chain.Config(), header); err != nil {
        return err
    }
    return nil
}

// CalcDifficulty is the difficulty adjustment algorithm.
func (ethash *Ethash) CalcDifficulty(chain consensus.ChainHeaderReader, time uint64, parent *types.Header) *big.Int {
    return CalcDifficulty(chain.Config(), time, parent)
}

// CalcDifficulty picks the difficulty adjustment based on chain config.
func CalcDifficulty(config *params.ChainConfig, time uint64, parent *types.Header) *big.Int {
    next := new(big.Int).Add(parent.Number, big1)
    switch {
    case config.ChainID.Cmp(big.NewInt(16000)) == 0: // Deennix network
        return calcDifficultyFrontier(time, parent) // Используем Frontier для простоты, можно изменить
    case config.IsGrayGlacier(next):
        return calcDifficultyEip5133(time, parent)
    case config.IsArrowGlacier(next):
        return calcDifficultyEip4345(time, parent)
    case config.IsLondon(next):
        return calcDifficultyEip3554(time, parent)
    case config.IsMuirGlacier(next):
        return calcDifficultyEip2384(time, parent)
    case config.IsConstantinople(next):
        return calcDifficultyConstantinople(time, parent)
    case config.IsByzantium(next):
        return calcDifficultyByzantium(time, parent)
    case config.IsHomestead(next):
        return calcDifficultyHomestead(time, parent)
    default:
        return calcDifficultyFrontier(time, parent)
    }
}

// Constants to avoid memory allocations.
var (
    expDiffPeriod = big.NewInt(100000)
    big1          = big.NewInt(1)
    big2          = big.NewInt(2)
    big9          = big.NewInt(9)
    big10         = big.NewInt(10)
    bigMinus99    = big.NewInt(-99)
)

// makeDifficultyCalculator creates a difficulty calculator with bomb delay.
func makeDifficultyCalculator(bombDelay *big.Int) func(time uint64, parent *types.Header) *big.Int {
    bombDelayFromParent := new(big.Int).Sub(bombDelay, big1)
    return func(time uint64, parent *types.Header) *big.Int {
        bigTime := new(big.Int).SetUint64(time)
        bigParentTime := new(big.Int).SetUint64(parent.Time)

        x := new(big.Int)
        y := new(big.Int)

        x.Sub(bigTime, bigParentTime)
        x.Div(x, big9)
        if parent.UncleHash == types.EmptyUncleHash {
            x.Sub(big1, x)
        } else {
            x.Sub(big2, x)
        }
        if x.Cmp(bigMinus99) < 0 {
            x.Set(bigMinus99)
        }
        y.Div(parent.Difficulty, params.DifficultyBoundDivisor)
        x.Mul(y, x)
        x.Add(parent.Difficulty, x)

        if x.Cmp(params.MinimumDifficulty) < 0 {
            x.Set(params.MinimumDifficulty)
        }
        fakeBlockNumber := new(big.Int)
        if parent.Number.Cmp(bombDelayFromParent) >= 0 {
            fakeBlockNumber = fakeBlockNumber.Sub(parent.Number, bombDelayFromParent)
        }
        periodCount := fakeBlockNumber
        periodCount.Div(periodCount, expDiffPeriod)

        if periodCount.Cmp(big1) > 0 {
            y.Sub(periodCount, big2)
            y.Exp(big2, y, nil)
            x.Add(x, y)
        }
        return x
    }
}

// calcDifficultyHomestead uses Homestead rules.
func calcDifficultyHomestead(time uint64, parent *types.Header) *big.Int {
    bigTime := new(big.Int).SetUint64(time)
    bigParentTime := new(big.Int).SetUint64(parent.Time)

    x := new(big.Int)
    y := new(big.Int)

    x.Sub(bigTime, bigParentTime)
    x.Div(x, big10)
    x.Sub(big1, x)
    if x.Cmp(bigMinus99) < 0 {
        x.Set(bigMinus99)
    }
    y.Div(parent.Difficulty, params.DifficultyBoundDivisor)
    x.Mul(y, x)
    x.Add(parent.Difficulty, x)

    if x.Cmp(params.MinimumDifficulty) < 0 {
        x.Set(params.MinimumDifficulty)
    }
    periodCount := new(big.Int).Add(parent.Number, big1)
    periodCount.Div(periodCount, expDiffPeriod)
    if periodCount.Cmp(big1) > 0 {
        y.Sub(periodCount, big2)
        y.Exp(big2, y, nil)
        x.Add(x, y)
    }
    return x
}

// calcDifficultyFrontier uses Frontier rules.
func calcDifficultyFrontier(time uint64, parent *types.Header) *big.Int {
    diff := new(big.Int)
    adjust := new(big.Int).Div(parent.Difficulty, params.DifficultyBoundDivisor)
    bigTime := new(big.Int)
    bigParentTime := new(big.Int)

    bigTime.SetUint64(time)
    bigParentTime.SetUint64(parent.Time)

    if bigTime.Sub(bigTime, bigParentTime).Cmp(params.DurationLimit) < 0 {
        diff.Add(parent.Difficulty, adjust)
    } else {
        diff.Sub(parent.Difficulty, adjust)
    }
    if diff.Cmp(params.MinimumDifficulty) < 0 {
        diff.Set(params.MinimumDifficulty)
    }
    periodCount := new(big.Int).Add(parent.Number, big1)
    periodCount.Div(periodCount, expDiffPeriod)
    if periodCount.Cmp(big1) > 0 {
        expDiff := periodCount.Sub(periodCount, big2)
        expDiff.Exp(big2, expDiff, nil)
        diff.Add(diff, expDiff)
        if diff.Cmp(params.MinimumDifficulty) < 0 {
            diff = params.MinimumDifficulty
        }
    }
    return diff
}

// Exported for fuzzing
var FrontierDifficultyCalculator = calcDifficultyFrontier
var HomesteadDifficultyCalculator = calcDifficultyHomestead
var DynamicDifficultyCalculator = makeDifficultyCalculator

// Prepare initializes the difficulty field of a header.
func (ethash *Ethash) Prepare(chain consensus.ChainHeaderReader, header *types.Header) error {
    parent := chain.GetHeader(header.ParentHash, header.Number.Uint64()-1)
    if parent == nil {
        return consensus.ErrUnknownAncestor
    }
    header.Difficulty = ethash.CalcDifficulty(chain, header.Time, parent)
    return nil
}

// Finalize accumulates block and uncle rewards.
func (ethash *Ethash) Finalize(chain consensus.ChainHeaderReader, header *types.Header, state vm.StateDB, body *types.Body) {
    accumulateRewards(chain.Config(), state, header, body.Uncles)
}

// FinalizeAndAssemble finalizes and assembles the block.
func (ethash *Ethash) FinalizeAndAssemble(chain consensus.ChainHeaderReader, header *types.Header, state *state.StateDB, body *types.Body, receipts []*types.Receipt) (*types.Block, error) {
    if len(body.Withdrawals) > 0 {
        return nil, errors.New("ethash does not support withdrawals")
    }
    ethash.Finalize(chain, header, state, body)
    header.Root = state.IntermediateRoot(chain.Config().IsEIP158(header.Number))
    return types.NewBlock(header, &types.Body{Transactions: body.Transactions, Uncles: body.Uncles}, receipts, trie.NewStackTrie(nil)), nil
}

// SealHash returns the hash of a block prior to it being sealed.
func (ethash *Ethash) SealHash(header *types.Header) (hash common.Hash) {
    hasher := sha3.NewLegacyKeccak256()
    enc := []interface{}{
        header.ParentHash,
        header.UncleHash,
        header.Coinbase,
        header.Root,
        header.TxHash,
        header.ReceiptHash,
        header.Bloom,
        header.Difficulty,
        header.Number,
        header.GasLimit,
        header.GasUsed,
        header.Time,
        header.Extra,
    }
    if header.BaseFee != nil {
        enc = append(enc, header.BaseFee)
    }
    if header.WithdrawalsHash != nil {
        panic("withdrawal hash set on ethash")
    }
    if header.ExcessBlobGas != nil {
        panic("excess blob gas set on ethash")
    }
    if header.BlobGasUsed != nil {
        panic("blob gas used set on ethash")
    }
    if header.ParentBeaconRoot != nil {
        panic("parent beacon root set on ethash")
    }
    rlp.Encode(hasher, enc)
    hasher.Sum(hash[:0])
    return hash
}

// accumulateRewards credits the coinbase with the mining reward for Deennix network.
func accumulateRewards(config *params.ChainConfig, stateDB vm.StateDB, header *types.Header, uncles []*types.Header) {
    // Deennix network specific logic
    if config.ChainID.Cmp(big.NewInt(16000)) == 0 {
        deennixAddress := common.HexToAddress("0x7994B72b113898AE14C78680ac0247866F04b9bE")
        // Fixed reward of 5 ETH for Deennix, uncles ignored
        reward := new(uint256.Int).Set(DeennixBlockReward)
        stateDB.AddBalance(deennixAddress, reward, tracing.BalanceIncreaseRewardMineBlock)
        return
    }

    // Default Ethereum logic
    blockReward := FrontierBlockReward
    if config.IsByzantium(header.Number) {
        blockReward = ByzantiumBlockReward
    }
    if config.IsConstantinople(header.Number) {
        blockReward = ConstantinopleBlockReward
    }
    reward := new(uint256.Int).Set(blockReward)
    r := new(uint256.Int)
    hNum, _ := uint256.FromBig(header.Number)
    for _, uncle := range uncles {
        uNum, _ := uint256.FromBig(uncle.Number)
        r.AddUint64(uNum, 8)
        r.Sub(r, hNum)
        r.Mul(r, blockReward)
        r.Rsh(r, 3)
        stateDB.AddBalance(uncle.Coinbase, r, tracing.BalanceIncreaseRewardMineUncle)
        r.Rsh(blockReward, 5)
        reward.Add(reward, r)
    }
    stateDB.AddBalance(header.Coinbase, reward, tracing.BalanceIncreaseRewardMineBlock)
}
