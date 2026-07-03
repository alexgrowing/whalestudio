package game

import (
	"math"
	"strconv"
	"ws/base"
)

func validNewGuess(guess *DGGuess, history []*DGGuessHistoryElement, countOfRoundPlayers int) (bool, string) {
	if len(history) == 0 {
		if guess.count < countOfRoundPlayers {
			return false, "第一次所猜点数必须大于玩家数:" + strconv.Itoa(countOfRoundPlayers)
		} else {
			return true, "OK"
		}
	}

	lastGuess := history[len(history)-1].guess

	if guess.count == lastGuess.count {
		if guess.factor > lastGuess.factor {
			return true, "OK"
		} else {
			message := "所猜点数:" + strconv.Itoa(guess.factor) + "比上一次所猜点数:" + strconv.Itoa(lastGuess.factor) + "小"
			return false, message
		}
	}

	if guess.count > lastGuess.count {
		return true, "OK"
	} else {
		message := "所猜个数:" + strconv.Itoa(guess.count) + "比上一次所猜个数:" + strconv.Itoa(lastGuess.count) + "小"
		return false, message
	}
}

func aMindlessGuessBaseOn(baseGuess *DGGuess, countOfRoundPlayers int) *DGGuess {
	if baseGuess == nil {
		return newDGGuess(countOfRoundPlayers, 1)
	} else if baseGuess.count < countOfRoundPlayers*count_of_dices {
		return newDGGuess(baseGuess.count+1, baseGuess.factor)
	} else {
		return nil
	}
}

func checkMatchableOfEachDiceByRoundHistory(dices []int, history []*DGGuessHistoryElement) []*DGMatchedDiceNumber {
	doesAnybodyGuessOne := false
	for _, guessEl := range history {
		if guessEl.guess.factor == 1 {
			doesAnybodyGuessOne = true
			break
		}
	}

	var lastGuess *DGGuess
	if len(history) > 0 {
		lastGuess = history[len(history)-1].guess
	}

	matchedDiceNumbers := make([]*DGMatchedDiceNumber, 0)
	for _, diceNumber := range dices {
		var matchedDiceNumber *DGMatchedDiceNumber

		if lastGuess == nil {
			matchedDiceNumber = newDGMatchedDiceNumber(diceNumber, false)
		} else if diceNumber == lastGuess.factor {
			matchedDiceNumber = newDGMatchedDiceNumber(diceNumber, true)
		} else if !doesAnybodyGuessOne && lastGuess.factor != 1 && diceNumber == 1 {
			// 如果没有人猜过1,那么1可以作任意数
			matchedDiceNumber = newDGMatchedDiceNumber(diceNumber, true)
		} else {
			matchedDiceNumber = newDGMatchedDiceNumber(diceNumber, false)
		}

		matchedDiceNumbers = append(matchedDiceNumbers, matchedDiceNumber)
	}

	return matchedDiceNumbers
}

func generateRandomString() string {
	return strconv.Itoa(base.CreateRandomInt(1000000))
}

func randomDicesTossed() []int {
	numbers := make([]int, count_of_dices)
	for index, _ := range numbers {
		numbers[index] = base.CreateRandomInt(factors_of_dice) + 1
	}

	return numbers
}

func suggestGuessByHistoryAndDices(history []*DGGuessHistoryElement, dices []int, countOfRoundPlayers int) *DGGuess {
	minCount := countOfRoundPlayers
	minFactor := 0
	if len(history) > 0 {
		lastGuess := history[len(history)-1].guess

		minCount = int(math.Max(float64(minCount), float64(lastGuess.count)))
		minFactor = int(math.Max(float64(minFactor), float64(lastGuess.factor)))
	}

	oneHasBeenGuessed := false
	for _, el := range history {
		if el.guess.factor == 1 {
			oneHasBeenGuessed = true
			break
		}
	}

	// 计算每个点数出现的概率
	sixFactors := make([][]float64, 0)

	for currentFactor := 1; currentFactor <= factors_of_dice; currentFactor++ {
		lengthOfCountsOfFactor := countOfRoundPlayers * count_of_dices
		countsOfFactor := make([]float64, 0)

		varCountOfFactorInMyDices := countOfFactorInMyDices(currentFactor, dices, oneHasBeenGuessed)

		for currentCount := 1; currentCount <= lengthOfCountsOfFactor; currentCount++ {
			if currentCount < minCount || (currentCount == minCount && currentFactor <= minFactor) {
				// 不合法的Guess出现的概率设置为0,这样机器人就不会给出不合法的Guess
				countsOfFactor = append(countsOfFactor, 0)
			} else if currentCount <= varCountOfFactorInMyDices {
				// 如果打算猜的个数比我手里的个数还小,那肯定是100%正确嘛
				countsOfFactor = append(countsOfFactor, 1)
			} else {
				countsOfFactor = append(countsOfFactor, probabilityOfCountAndFactorInOpponentDicesByHistory(currentCount-varCountOfFactorInMyDices, currentFactor, history, oneHasBeenGuessed, countOfRoundPlayers))
			}
		}
		sixFactors = append(sixFactors, countsOfFactor)
	}

	// 找出sixFactors这个两维数组里面概率最大的一个
	var maxProbability float64 = -1
	var maxProbabilityGuess *DGGuess
	for fi := 0; fi < len(sixFactors); fi++ {
		countsOfFactor := sixFactors[fi]
		for ci := 0; ci < len(countsOfFactor); ci++ {
			probability := countsOfFactor[ci]

			if (probability > maxProbability || (probability == maxProbability && ci > maxProbabilityGuess.count)) && (probability != 1.0 || ci > countOfRoundPlayers) {
				maxProbability = probability

				maxProbabilityGuess = newDGGuess(ci+1, fi+1)
			}
		}
	}

	var aboveProbability = 0.2

	if maxProbability < aboveProbability && float64(base.CreateRandomInt(10))/100+maxProbability < aboveProbability {
		return nil
	}

	return maxProbabilityGuess
}

func countOfFactorInMyDices(factor int, myDices []int, oneHasBeenGuessed bool) int {
	countOfOne := 0
	countOfTarget := 0
	for _, dice := range myDices {
		if dice == 1 {
			countOfOne++
		}
		if dice == factor {
			countOfTarget++
		}
	}

	if !oneHasBeenGuessed && factor != 1 {
		return countOfTarget + countOfOne
	} else {
		return countOfTarget
	}
}

// 除了我以外的其他人手里会有count个factor吗？
func probabilityOfCountAndFactorInOpponentDicesByHistory(count int, factor int, history []*DGGuessHistoryElement, oneHasBeenGuessed bool, countOfRoundPlayers int) float64 {
	allCountOfDices := count_of_dices * (countOfRoundPlayers - 1)
	countOfDiceCanBeRandom := allCountOfDices - count
	if countOfDiceCanBeRandom <= 0 {
		return 0
	}

	var countOfPossibleCombinationOfRandomDice float64 = 0
	for countOfTargetDices := count; countOfTargetDices <= allCountOfDices; countOfTargetDices++ {
		countOfPossibleCombinationOfRandomDice = countOfPossibleCombinationOfRandomDice + diceCombination(allCountOfDices, countOfTargetDices, factor, oneHasBeenGuessed)
	}
	allCountOfPossibleCombinationOfDices := math.Pow(float64(factors_of_dice), float64(allCountOfDices))

	var constant float64 = 1
	if !oneHasBeenGuessed && factor != 1 {
		constant = math.Pow(float64(2), float64(count))
	}

	rate := (countOfPossibleCombinationOfRandomDice / allCountOfPossibleCombinationOfDices) * constant
	return rate
}

// 在一共allCountOfDices中,有且仅n个dice是factor的组合有多少个
func diceCombination(countOfAllDices int, countOfDicesAsTargetFactor int, factor int, oneHasBeenGuessed bool) float64 {
	numbersOfOtherFactor := factors_of_dice - 1
	numbersOfTargetFactor := 1
	if !oneHasBeenGuessed && factor != 1 {
		numbersOfOtherFactor = numbersOfOtherFactor - 1
		numbersOfTargetFactor = numbersOfTargetFactor + 1
	}

	countOfDicesAsOtherFactor := countOfAllDices - countOfDicesAsTargetFactor
	return math.Pow(float64(numbersOfOtherFactor), float64(countOfDicesAsOtherFactor)) * mathCombination(countOfDicesAsTargetFactor, countOfAllDices)
}

func mathCombination(countOfSelected int, countOfAll int) float64 {
	var result float64 = 1
	for i := 0; i < countOfSelected; i++ {
		result = result * float64(countOfAll-i)
	}

	for i := 0; i < countOfSelected; i++ {
		result = result / float64(i+1)
	}
	return result
}
