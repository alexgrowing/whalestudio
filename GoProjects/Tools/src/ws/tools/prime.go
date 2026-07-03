package tools

import (
	"math"
	"math/big"
)

// TestBigNumber 测试一个大数是不是素数
func TestBigNumber() {
	var i64, e64, m64 int64 = 5, 6546640, 12830603
	// var i64, e64, m64 int64 = 2, 1213123130, 1213123131

	var i, e, m = big.NewInt(i64), big.NewInt(e64), big.NewInt(m64)
	i.Exp(i, e, m)
	println("result from golang.big:", i.Int64())

	modBigNumber(i64, e64, m64)
}

func modBigNumber(baseNumber int64, powerNumber int64, modNumber int64) int64 {
	splitedPowerNumbers := seperatePowerNumber(powerNumber)

	largestPP := splitedPowerNumbers[0]
	modTable := make([]int64, largestPP+1)

	for i := 0; i < len(modTable); i++ {
		if i == 0 {
			modTable[i] = int64(math.Mod(math.Pow(float64(baseNumber), math.Pow(2, float64(i))), float64(modNumber)))
		} else {
			modTable[i] = int64(math.Mod(math.Pow(float64(modTable[i-1]), 2), float64(modNumber)))
		}
	}
	// println("----------------")
	// for i, m := range modTable {
	// 	println(strconv.Itoa(int(baseNumber)) + "^(2^" + strconv.Itoa(i) + ")=" + strconv.Itoa(int(m)))
	// }

	var finalResult int64 = 1
	for i := len(splitedPowerNumbers) - 1; i >= 0; i-- {
		tmp := float64(finalResult * modTable[splitedPowerNumbers[i]])
		finalResult = int64(math.Mod(tmp, float64(modNumber)))
	}
	println("result from self calculate:", finalResult)

	return finalResult
}

func seperatePowerNumber(powerNumber int64) []int64 {
	ret := make([]int64, 0)
	for powerNumber > 0 {
		newNumber := int64(math.Log2(float64(powerNumber)))
		ret = append(ret, newNumber)
		powerNumber = powerNumber - int64(math.Pow(2, float64(newNumber)))
	}

	// for _, n := range ret {
	// 	println(n)
	// }
	return ret
}
