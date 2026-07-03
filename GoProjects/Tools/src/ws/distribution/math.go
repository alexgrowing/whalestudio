package distribution

import (
	"fmt"
	"math"
	"math/big"
)

// Factorial Factorial
func Factorial(n int64) *big.Int {
	return _factorial(1, n)
}

func _factorial(from int64, to int64) *big.Int {
	return big.NewInt(0).MulRange(from, to)
}

// Combine Combine
func Combine(n int64, k int64) *big.Int {
	return big.NewInt(0).Div(_factorial(n-k+1, n), Factorial(k))
}

// TrustCalc TrustCalc
func TrustCalc(smallN int64, matchInSmallN int64, bigN int64) {
	expect := float64(matchInSmallN) / float64(smallN)
	matchInBigN := int64(float64(bigN) * expect)
	countOfSelections := make([]*big.Int, 0)

	sum := big.NewInt(0)
	for mi := int64(0); mi <= smallN; mi++ {
		iCount := countOfSelection(bigN, matchInBigN, smallN, mi)
		countOfSelections = append(countOfSelections, iCount)
		sum = sum.Add(sum, iCount)
		// fmt.Printf("%2d=%v\n", mi, iCount)
	}

	probabilityOfSelections := make([]float64, 0)
	deviation := float64(0)
	for ci := 0; ci < len(countOfSelections); ci++ {
		cs := countOfSelections[ci]
		cs = cs.Mul(cs, big.NewInt(100000000)).Div(cs, sum)
		probability := float64(cs.Int64()) / 100000000
		probabilityOfSelections = append(probabilityOfSelections, probability)

		deviation = deviation + math.Pow((float64(ci)/float64(smallN)-expect), 2)*probability
		// fmt.Printf("probability[%2d]=%.8f\n", ci, probabilityOfSelections[ci])
	}
	deviation = math.Sqrt(deviation)

	fmt.Printf("在总体为%d的个体中抽样%d个,符合条件的有%d个\n", bigN, smallN, matchInSmallN)
	fmt.Printf("期望：%.2f%%\n", expect*float64(100))
	fmt.Printf("标准差：%.2f%%\n", deviation*float64(100))

	fmt.Printf("区间%.2f%% ~ %.2f%%的置信度为68.26%%\n", (expect-deviation)*float64(100), (expect+deviation)*float64(100))
	fmt.Printf("区间%.2f%% ~ %.2f%%的置信度为90%%\n", (expect-1.65*deviation)*float64(100), (expect+1.65*deviation)*float64(100))
	fmt.Printf("区间%.2f%% ~ %.2f%%的置信度为95%%\n", (expect-1.96*deviation)*float64(100), (expect+1.96*deviation)*float64(100))
	fmt.Printf("区间%.2f%% ~ %.2f%%的置信度为95.44%%\n", (expect-2*deviation)*float64(100), (expect+2*deviation)*float64(100))
	fmt.Printf("区间%.2f%% ~ %.2f%%的置信度为99%%\n", (expect-2.58*deviation)*float64(100), (expect+2.58*deviation)*float64(100))
	fmt.Printf("区间%.2f%% ~ %.2f%%的置信度为99.72%%\n", (expect-3*deviation)*float64(100), (expect+3*deviation)*float64(100))
}

func countOfSelection(bigN int64, matchInBigN int64, smallN int64, matchInSmallN int64) *big.Int {
	combineOfMatch := Combine(matchInBigN, matchInSmallN)
	combineOfUnmatch := Combine(bigN-matchInBigN, smallN-matchInSmallN)

	return big.NewInt(0).Mul(combineOfMatch, combineOfUnmatch)
}
