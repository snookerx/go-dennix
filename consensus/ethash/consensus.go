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
    "bytes"
    "errors"
    "fmt"
    "math/big"
    "runtime"
    "time"

    mapset "github.com/deckarep/golang-set/v2"
    "github.com/ethereum/go-ethereum/common"
    "github.com/ethereum/go-ethereum/common/math"
    "github.com/ethereum/go-ethereum/consensus"
    "github.com/ethereum/go-ethereum/consensus/misc"
    "github.com/ethereum/go-ethereum/core/state"
    "github.com/ethereum/go-ethereum/core/types"
    "github.com/ethereum/go-ethereum/params"
    "github.com/ethereum/go-ethereum/rlp"
    "github.com/ethereum/go-ethereum/trie"
    "golang.org/x/crypto/sha3"
)

// -----------------------------------------------------------------------------
// Dennix Config to block reward schedule and fees:
//
// 1) No uncle rewards are paid.
//
// 2) Block reward schedule (values in DEN, each * 1e18):
//    - block            1 to 500,000: 100 DEN
//    - block    500,001 to 1,000,000: 50 DEN
//    - block  1,000,001 to 2,000,000: 25 DEN
//    - block  2,000,001 to 5,000,000: 10 DEN
//    - block 5,000,001 to 75,000,000: 1 DEN
//    - after 75,000,000             : 0 DEN
//
//    This ensures a maximum total supply ~200 million DEN.
//
// 3) Foundation fee (10%) + Development fee (10%) => total of 20% is taken
//    out of the block reward (no extra emission). E.g. if block reward is 100 DEN,
//    the miner receives 80 DEN, foundation wallet 10 DEN, and development wallet 10 DEN.
//
// 4) Difficulty adjustment for 'Dennix' fork is forced to aim for ~5s block time.

// Ethash proof-of-work protocol constants.
var (
    FrontierBlockReward       = big.NewInt(5e+18) // (unused in custom fork)
    ByzantiumBlockReward      = big.NewInt(3e+18) // (unused in custom fork)
    ConstantinopleBlockReward = big.NewInt(2e+18) // (unused in custom fork)
    maxUncles                 = 2                 // Maximum number of uncles (still verified, but reward = 0)
    allowedFutureBlockTimeSeconds = int64(5)      // Adjusted for ~5s block time target in Dennix

    // We keep these EIP calculators around in case other forks are used or needed,
    // but they won't matter much if you skip older forks or only run "Dennix".
    calcDifficultyEip5133        = makeDifficultyCalculator(big.NewInt(11_400_000))
    calcDifficultyEip4345        = makeDifficultyCalculator(big.NewInt(10_700_000))
    calcDifficultyEip3554        = makeDifficultyCalculator(big.NewInt(9_700_000))
    calcDifficultyEip2384        = makeDifficultyCalculator(big.NewInt(9_000_000))
    calcDifficultyConstantinople = makeDifficultyCalculator(big.NewInt(5_000_000))
    calcDifficultyByzantium      = makeDifficultyCalculator(big.NewInt(3_000_000))
)

// Various error messages
var (
    errOlderBlockTime    = errors.New("timestamp older than parent")
    errTooManyUncles     = errors.New("too many uncles")
    errDuplicateUncle    = errors.New("duplicate uncle")
    errUncleIsAncestor   = errors.New("uncle is ancestor")
    errDanglingUncle     = errors.New("uncle's parent is not ancestor")
    errInvalidDifficulty = errors.New("non-positive difficulty")
    errInvalidMixDigest  = errors.New("invalid mix digest")
    errInvalidPoW        = errors.New("invalid proof-of-work")
)

// Author implements consensus.Engine, returning the header's coinbase as the
// proof-of-work verified author of the block.
func (ethash *Ethash) Author(header *types.Header) (common.Address, error) {
    return header.Coinbase, nil
}

// VerifyHeader checks whether a header conforms to the consensus rules of the
// stock Ethereum ethash engine.
func (ethash *Ethash) VerifyHeader(chain consensus.ChainHeaderReader, header *types.Header, seal bool) error {
    if ethash.config.PowMode == ModeFullFake {
        return nil
    }
    number := header.Number.Uint64()
    if chain.GetHeader(header.Hash(), number) != nil {
        return nil
    }
    parent := chain.GetHeader(header.ParentHash, number-1)
    if parent == nil {
        return consensus.ErrUnknownAncestor
    }
    return ethash.verifyHeader(chain, header, parent, false, seal, time.Now().Unix())
}

// VerifyHeaders is similar to VerifyHeader, but verifies a batch of headers
// concurrently. The method returns a quit channel to abort the operations and
// a results channel to retrieve the async verifications.
func (ethash *Ethash) VerifyHeaders(chain consensus.ChainHeaderReader, headers []*types.Header, seals []bool) (chan<- struct{}, <-chan error) {
    if ethash.config.PowMode == ModeFullFake || len(headers) == 0 {
        abort, results := make(chan struct{}), make(chan error, len(headers))
        for i := 0; i < len(headers); i++ {
            results <- nil
        }
        return abort, results
    }

    workers := runtime.GOMAXPROCS(0)
    if len(headers) < workers {
        workers = len(headers)
    }

    var (
        inputs  = make(chan int)
        done    = make(chan int, workers)
        errors  = make([]error, len(headers))
        abort   = make(chan struct{})
        unixNow = time.Now().Unix()
    )
    for i := 0; i < workers; i++ {
        go func() {
            for index := range inputs {
                errors[index] = ethash.verifyHeaderWorker(chain, headers, seals, index, unixNow)
                done <- index
            }
        }()
    }

    errorsOut := make(chan error, len(headers))
    go func() {
        defer close(inputs)
        var (
            in, out = 0, 0
            checked = make([]bool, len(headers))
            inputsC = inputs
        )
        for {
            select {
            case inputsC <- in:
                in++
                if in == len(headers) {
                    inputsC = nil
                }
            case index := <-done:
                for checked[index] = true; checked[out]; out++ {
                    errorsOut <- errors[out]
                    if out == len(headers)-1 {
                        return
                    }
                }
            case <-abort:
                return
            }
        }
    }()
    return abort, errorsOut
}

func (ethash *Ethash) verifyHeaderWorker(chain consensus.ChainHeaderReader, headers []*types.Header, seals []bool, index int, unixNow int64) error {
    var parent *types.Header
    if index == 0 {
        parent = chain.GetHeader(headers[0].ParentHash, headers[0].Number.Uint64()-1)
    } else if headers[index-1].Hash() == headers[index].ParentHash {
        parent = headers[index-1]
    }
    if parent == nil {
        return consensus.ErrUnknownAncestor
    }
    return ethash.verifyHeader(chain, headers[index], parent, false, seals[index], unixNow)
}

// VerifyUncles verifies that the given block's uncles conform to the consensus
// rules of the stock Ethereum ethash engine. (We still verify them, but reward=0)
func (ethash *Ethash) VerifyUncles(chain consensus.ChainReader, block *types.Block) error {
    if ethash.config.PowMode == ModeFullFake {
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
        if err := ethash.verifyHeader(chain, uncle, ancestors[uncle.ParentHash], true, true, time.Now().Unix()); err != nil {
            return err
        }
    }
    return nil
}

// verifyHeader checks whether a header conforms to the consensus rules of the
// stock Ethereum ethash engine.
func (ethash *Ethash) verifyHeader(chain consensus.ChainHeaderReader, header, parent *types.Header, uncle bool, seal bool, unixNow int64) error {
    if uint64(len(header.Extra)) > params.MaximumExtraDataSize {
        return fmt.Errorf("extra-data too long: %d > %d", len(header.Extra), params.MaximumExtraDataSize)
    }
    // For "Dennix" fork, check that mixDigest is zero
    if chain.Config().IsDennix(header.Number) && header.MixDigest != (common.Hash{}) {
        return fmt.Errorf("mix digest should be zero value after dennix fork, %v", header.MixDigest)
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
    } else if err := misc.VerifyEip1559Header(chain.Config(), parent, header); err != nil {
        return err
    }
    diff := new(big.Int).Sub(header.Number, parent.Number)
    if diff.Cmp(big.NewInt(1)) != 0 {
        return consensus.ErrInvalidNumber
    }
    if chain.Config().IsShanghai(header.Time) {
        return fmt.Errorf("ethash does not support shanghai fork")
    }
    if chain.Config().IsCancun(header.Time) {
        return fmt.Errorf("ethash does not support cancun fork")
    }
    if seal {
        if err := ethash.verifySeal(chain, header, false); err != nil {
            return err
        }
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

// CalcDifficulty picks the correct difficulty function based on the chain config.
func CalcDifficulty(config *params.ChainConfig, time uint64, parent *types.Header) *big.Int {
    next := new(big.Int).Add(parent.Number, big1)
    switch {
    case config.IsDennix(next):
        // Custom "Dennix" difficulty => target 5s blocks
        return calcDifficultyDennix(time, parent)
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

// Constants to help with difficulty calculations
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
            fakeBlockNumber.Sub(parent.Number, bombDelayFromParent)
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

// calcDifficultyDennix implements a custom difficulty that targets ~5s blocks
// and ignores uncles for difficulty adjustments.
func calcDifficultyDennix(time uint64, parent *types.Header) *big.Int {
    bigTime := new(big.Int).SetUint64(time)
    bigParentTime := new(big.Int).SetUint64(parent.Time)

    x := new(big.Int)
    y := new(big.Int)

    // "target blocktime" = 5
    // difference = (time - parent.time) / 5
    x.Sub(bigTime, bigParentTime)
    x.Div(x, big.NewInt(5))

    // We ignore uncles in difficulty adjustment: always do (1 - x)
    x.Sub(big.NewInt(1), x)

    // clamp to -99
    if x.Cmp(bigMinus99) < 0 {
        x.Set(bigMinus99)
    }
    y.Div(parent.Difficulty, params.DifficultyBoundDivisor)
    x.Mul(y, x)
    x.Add(parent.Difficulty, x)

    // Enforce minimum difficulty
    if x.Cmp(params.MinimumDifficulty) < 0 {
        x.Set(params.MinimumDifficulty)
    }
    // We remove the exponential bomb for Dennix => no additional factor
    return x
}

// calcDifficultyHomestead uses the Homestead rules.
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

// calcDifficultyFrontier uses the Frontier rules.
func calcDifficultyFrontier(time uint64, parent *types.Header) *big.Int {
    diff := new(big.Int)
    adjust := new(big.Int).Div(parent.Difficulty, params.DifficultyBoundDivisor)
    bigTime := new(big.Int).SetUint64(time)
    bigParentTime := new(big.Int).SetUint64(parent.Time)

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
        diff = math.BigMax(diff, params.MinimumDifficulty)
    }
    return diff
}

// Exported for fuzzing
var (
    FrontierDifficultyCalculator  = calcDifficultyFrontier
    HomesteadDifficultyCalculator = calcDifficultyHomestead
    DynamicDifficultyCalculator   = makeDifficultyCalculator
)

// verifySeal checks whether a block satisfies the PoW difficulty requirements.
func (ethash *Ethash) verifySeal(chain consensus.ChainHeaderReader, header *types.Header, fulldag bool) error {
    if ethash.config.PowMode == ModeFake || ethash.config.PowMode == ModeFullFake {
        time.Sleep(ethash.fakeDelay)
        if ethash.fakeFail == header.Number.Uint64() {
            return errInvalidPoW
        }
        return nil
    }
    if ethash.shared != nil {
        return ethash.shared.verifySeal(chain, header, fulldag)
    }
    if header.Difficulty.Sign() <= 0 {
        return errInvalidDifficulty
    }
    number := header.Number.Uint64()
    var result []byte

    if chain == nil || chain.Config().IsDennix(header.Number) {
        // Custom path for "Dennix" (post-PoW?)
        hashSource := make([]byte, 0, common.HashLength*2+8)
        hashSource = append(hashSource, ethash.SealHash(header).Bytes()...)
        hashSource = append(hashSource, seedHash(number)...)
        hashSource = append(hashSource, header.Nonce[:]...)
        arrResult := dennixHash(hashSource)
        result = arrResult[:]
    } else {
        var digest []byte
        if fulldag {
            dataset := ethash.dataset(number, true)
            if dataset.generated() {
                digest, result = hashimotoFull(dataset.dataset, ethash.SealHash(header).Bytes(), header.Nonce.Uint64())
                runtime.KeepAlive(dataset)
            } else {
                fulldag = false
            }
        }
        if !fulldag {
            cache := ethash.cache(number)
            size := datasetSize(number)
            if ethash.config.PowMode == ModeTest {
                size = 64 * 1024
            }
            digest, result = hashimotoLight(size, cache.cache, ethash.SealHash(header).Bytes(), header.Nonce.Uint64())
            runtime.KeepAlive(cache)
        }
        if !bytes.Equal(header.MixDigest[:], digest) {
            return errInvalidMixDigest
        }
    }
    target := new(big.Int).Div(two256, header.Difficulty)
    if new(big.Int).SetBytes(result).Cmp(target) > 0 {
        return errInvalidPoW
    }
    return nil
}

// Prepare initializes the difficulty field of a header.
func (ethash *Ethash) Prepare(chain consensus.ChainHeaderReader, header *types.Header) error {
    parent := chain.GetHeader(header.ParentHash, header.Number.Uint64()-1)
    if parent == nil {
        return consensus.ErrUnknownAncestor
    }
    header.Difficulty = ethash.CalcDifficulty(chain, header.Time, parent)
    return nil
}

// Finalize applies block reward with no uncle reward.
func (ethash *Ethash) Finalize(
    chain consensus.ChainHeaderReader,
    header *types.Header,
    state *state.StateDB,
    txs []*types.Transaction,
    uncles []*types.Header,
    withdrawals []*types.Withdrawal,
) {
    accumulateRewards(chain.Config(), state, header)
}

// FinalizeAndAssemble applies block reward and assembles the block.
func (ethash *Ethash) FinalizeAndAssemble(
    chain consensus.ChainHeaderReader,
    header *types.Header,
    state *state.StateDB,
    txs []*types.Transaction,
    uncles []*types.Header,
    receipts []*types.Receipt,
    withdrawals []*types.Withdrawal,
) (*types.Block, error) {
    if len(withdrawals) > 0 {
        return nil, errors.New("ethash does not support withdrawals")
    }
    ethash.Finalize(chain, header, state, txs, uncles, nil)
    header.Root = state.IntermediateRoot(chain.Config().IsEIP158(header.Number))
    return types.NewBlock(header, txs, uncles, receipts, trie.NewStackTrie(nil)), nil
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
    rlp.Encode(hasher, enc)
    hasher.Sum(hash[:0])
    return hash
}

// Additional constants
var (
    big8  = big.NewInt(8)
    big32 = big.NewInt(32)
)

// -----------------------------------------------------------------------------
// Dennix block reward + foundation/development fee logic (uncle rewards removed).

// customRewardByNumber returns the base block reward (in wei) based on block number.
func customRewardByNumber(num *big.Int) *big.Int {
    n := num.Uint64()
    reward := new(big.Int)

    switch {
    case n >= 1 && n <= 500_000:
        // block 1 to 500,000 -> 100 DEN
        reward.SetUint64(100)
    case n <= 1_000_000:
        // 500,001 to 1,000,000 -> 50 DEN
        reward.SetUint64(50)
    case n <= 2_000_000:
        // 1,000,001 to 2,000,000 -> 25 DEN
        reward.SetUint64(25)
    case n <= 5_000_000:
        // 2,000,001 to 5,000,000 -> 10 DEN
        reward.SetUint64(10)
    case n <= 75_000_000:
        // 5,000,001 to 75,000,000 -> 1 DEN
        reward.SetUint64(1)
    default:
        // after 75,000,000 -> 0 DEN
        reward.SetUint64(0)
    }
    // convert to wei (DEN * 1e18)
    reward.Mul(reward, big.NewInt(1e18))
    return reward
}

// accumulateRewards pays block reward to the miner minus the foundation & development fees.
func accumulateRewards(config *params.ChainConfig, state *state.StateDB, header *types.Header) {
    blockNum := header.Number
    baseReward := customRewardByNumber(blockNum)
    if baseReward.Sign() == 0 {
        // No reward, no fees
        return
    }

    // Addresses for foundation and development
    foundationWallet := common.HexToAddress("0xe18c24638De283FE69d14149BBd0030b60d53300")
    developmentWallet := common.HexToAddress("0x7994B72b113898AE14C78680ac0247866F04b9bE")

    //
    // Split out 10% foundation fee + 10% development fee => 20% total
    //
    // If baseReward = 100 DEN, then each fee = 10 DEN, miner gets 80 DEN
    // So total reward emission is still 100 DEN, not 120 DEN.
    //

    tenPercent := new(big.Int).Div(
        new(big.Int).Mul(baseReward, big.NewInt(10)),
        big.NewInt(100),
    )
    // total 20% = (10 + 10)
    foundationFee := tenPercent
    developmentFee := tenPercent
    totalFees := new(big.Int).Add(foundationFee, developmentFee)

    // Miner gets the remainder
    minerReward := new(big.Int).Sub(baseReward, totalFees)

    // Pay miner
    state.AddBalance(header.Coinbase, minerReward)

    // Pay foundation
    if foundationFee.Sign() > 0 {
        state.AddBalance(foundationWallet, foundationFee)
    }

    // Pay development
    if developmentFee.Sign() > 0 {
        state.AddBalance(developmentWallet, developmentFee)
    }
}

// dennixHash is a placeholder for the custom hash function used in Dennix fork.
// Replace this with the actual implementation if needed.
func dennixHash(input []byte) [32]byte {
    hasher := sha3.NewLegacyKeccak256()
    hasher.Write(input)
    return [32]byte(hasher.Sum(nil))
}
