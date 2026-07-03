//
//  DGGameRules.swift
//  DiceGame
//
//  Created by Alex Chen on 15/4/24.
//  Copyright (c) 2015年 B & G. All rights reserved.
//

import Foundation

open class DGGameRules {
    static public let FACTOR_OF_DICE = 6
    static public let COUNT_OF_DICE = 5
    
    static public func randomDicesTossed() -> [Int] {
        var numbers = [Int]()
        for _ in 0 ..< COUNT_OF_DICE {
            numbers.append(1 + abs(arc4random().hashValue) % FACTOR_OF_DICE)
        }
        
        return numbers
    }
    
    static public func validateNewGuess(_ guess:DGGuess, history:[DGGuess], countOfFullPlayers:Int) -> DGMessageValidateNewGuess {
        if (history.count == 0) {
            if (guess.count < countOfFullPlayers) {
                return .firstGuessShouldLargerThanCountOfPlayers
            } else {
                return .ok;
            }
        }
        
        let lastGuess = history.last!
        
        if (guess.count == lastGuess.count) {
            if guess.factor > lastGuess.factor {
                return .ok
            } else {
                return .guessFactorShouldLargerThanLastGuess
            }
        }
        
        if (guess.count > lastGuess.count) {
            return .ok;
        } else {
            return .guessCountShouldLargerThanLastGuess
        }
    }
    
    /*
     * 根据这一局的历史,将掷的骰子添加Matched标识,从[Int]->[DGMatchedDiceNumber]
     */
    static public func checkMatchableOfEachDiceByRoundHistory(_ dices:[Int], history:[DGGuess]) -> [DGMatchedDiceNumber] {
        var doesAnybodyGuessOne:Bool = false
        for guess in history {
            if guess.factor == 1 {
                doesAnybodyGuessOne = true
                break
            }
        }
        
        let lastGuess = history.last!
        var matchedDiceNumbers = [DGMatchedDiceNumber]()
        for dIndex in 0 ..< dices.count {
            let valueOfDice = dices[dIndex]
            let matchedDiceNumber:DGMatchedDiceNumber
            if valueOfDice == lastGuess.factor {
                matchedDiceNumber = DGMatchedDiceNumber(diceNumber:valueOfDice, matched:true)
            }
            
            // 如果没有人猜过1,那么1可以作任意数
            else if !doesAnybodyGuessOne && lastGuess.factor != 1 && valueOfDice == 1 {
                matchedDiceNumber = DGMatchedDiceNumber(diceNumber:valueOfDice, matched:true)
            }
            else {
                matchedDiceNumber = DGMatchedDiceNumber(diceNumber:valueOfDice, matched:false)
            }
            
            matchedDiceNumbers.append(matchedDiceNumber)
        }
        
        return matchedDiceNumbers
    }
    
    // MARK : - Suggest Guess
    static public func suggestGuessByHistoryAndDices(_ history:[DGGuessHistoryElement], dices:[Int], countOfFullPlayers:Int) -> DGGuess? {
        var minCount = countOfFullPlayers;
        var minFactor = 0;
        if (history.count > 0) {
            let lastGuess = history.last!.guess
            minCount = max(minCount, lastGuess.count);
            minFactor = max(minFactor, lastGuess.factor);
        }
        
        var oneHasBeenGuessed = false
        for historyEl in history {
            if historyEl.guess.factor == 1 {
                oneHasBeenGuessed = true
                break
            }
        }
        
        // 计算每个点数出现的个数的概率
        var sixFactors = [[Float]]()
        for currentFactor in 1 ... FACTOR_OF_DICE {
            let lengthOfCountsOfFactor = countOfFullPlayers*COUNT_OF_DICE
            var countsOfFactor = [Float]()
            
            let countOfFactorInMyDices = DGGameRules.countOfFactorInMyDices(currentFactor, myDices: dices, oneHasBeenGuessed: oneHasBeenGuessed)
            for currentCount in 1 ... lengthOfCountsOfFactor {
                if currentCount < minCount || (currentCount == minCount && currentFactor <= minFactor) {
                    countsOfFactor.append(0)
                }
                else if (currentCount <= countOfFactorInMyDices) {
                    countsOfFactor.append(1)
                }
                else {
                    countsOfFactor.append(DGGameRules.probabilityOfCountAndFactorInOpponentDicesByHistory(currentCount-countOfFactorInMyDices, factor: currentFactor, history: history, oneHasBeenGuessed: oneHasBeenGuessed, countOfFullPlayers:countOfFullPlayers))
                }
            }
            
            sixFactors.append(countsOfFactor)
        }
        
        // 找出sixFactors这个两维数组里面概率最大的那一个
        var maxProbability:Float = -1
        var maxProbabilityGuess:DGGuess? = nil
        for fi in 0 ..< sixFactors.count {
            let countsOfFactor = sixFactors[fi]
            for ci in 0 ..< countsOfFactor.count {
                let probability = countsOfFactor[ci]
                
                if ((probability > maxProbability || (probability == maxProbability && ci > maxProbabilityGuess!.count)) && (probability != 1.0 || ci > countOfFullPlayers)) {
                    maxProbability = probability;
                    
                    maxProbabilityGuess = DGGuess(count: ci + 1, factor: fi + 1)
                }
            }
        }
        
        if maxProbability < 0.1 && Float((arc4random() % 10)) / 200 + maxProbability < 0.1 {
            return nil;
        }
        
        return maxProbabilityGuess;
    }
    
    fileprivate static func countOfFactorInMyDices(_ factor:Int, myDices:[Int], oneHasBeenGuessed:Bool) -> Int {
        var countOfOne = 0
        var countOfTarget = 0
        for dice in myDices {
            if dice == 1 {
                countOfOne += 1
            }
            if dice == factor {
                countOfTarget += 1
            }
        }
        
        if !oneHasBeenGuessed && factor != 1 {
            return countOfTarget + countOfOne
        } else {
            return countOfTarget
        }
    }
    
    fileprivate static func probabilityOfCountAndFactorInOpponentDicesByHistory(_ count:Int, factor:Int, history:[DGGuessHistoryElement], oneHasBeenGuessed:Bool, countOfFullPlayers:Int) -> Float {
        let allCountOfDices = COUNT_OF_DICE * (countOfFullPlayers-1)
        let countOfDiceCanBeRandom = allCountOfDices - count;
        if (countOfDiceCanBeRandom <= 0) {
            return 0.0;
        }
        
        let countOfPossibleCombinationOfRandomDice = powf(Float(FACTOR_OF_DICE), Float(countOfDiceCanBeRandom))
        let allCountOfPossibleCombinationOfDices = powf(Float(FACTOR_OF_DICE), Float(allCountOfDices))
        
        var constant:Float = 1.0;
        if !oneHasBeenGuessed && factor != 1 {
            constant = powf(2.0, Float(count))
        }
        
        return (countOfPossibleCombinationOfRandomDice / allCountOfPossibleCombinationOfDices) * constant;
    }
}

public enum DGMessageValidateNewGuess {
    case ok
    case firstGuessShouldLargerThanCountOfPlayers
    case guessFactorShouldLargerThanLastGuess
    case guessCountShouldLargerThanLastGuess
    
    public func description() -> String {
        switch self {
        case .ok:
            return "OK"
        case .firstGuessShouldLargerThanCountOfPlayers:
            return DGBundle.i18n(key:"First_Guess_Should_Be_Larger_Than_Count_Of_Players")
        case .guessFactorShouldLargerThanLastGuess:
            return DGBundle.i18n(key:"The_Point_Guessed_Is_Smaller_Than_Last_Guess")
        case .guessCountShouldLargerThanLastGuess:
            return DGBundle.i18n(key:"The_Count_Guessed_Is_Smaller_Than_Last_Guess")
        }
    }
}

// todo 这个enum与DGGameServer那边的几个Message有什么区别吗？
enum DGGameRulesMessage {
    case myID
    case iHaveTossedDice
    case myGuessNumberIs
    case myDicesAre
    case iBelieveLastGuessIsRight
}
