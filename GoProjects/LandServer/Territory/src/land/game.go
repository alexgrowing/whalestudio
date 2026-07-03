package land

import (
	"log"
	"math/rand"
	"time"
)

var randomGenerator = rand.New(rand.NewSource(time.Now().UnixNano()))

var PRICE_OF_EACH_SOLDIER = 100
var PRICE_OF_EACH_SOLDIER_2_CAMPAIGN = 2
var PRICE_OF_DIAMOND_2_RENAME = 10
var COUNT_OF_SOLDIER_TRAINING_PER_MINUTE = 10
var COUNT_OF_SECONDS_PER_DIAMOND = 200

var ERROR_NONE = 0
var ERROR_CODE_NOT_ENOUGH_DIAMOND = 1

func attack(attacker *Account, countOfSoldier int, goldCost int, target *Territory) *Fight {
	attackerWins := false
	countOfSoldierLoseOfWinner := 0
	countOfSoldierCaptivedByWinner := 0

	delta := countOfSoldier - target.ArmyQuantity*2
	log.Println("attacker:", countOfSoldier, ";defender:", target.ArmyQuantity, ";delta:", delta)
	if delta > 0 {
		attackerWins = true
		countOfSoldierLoseOfWinner = int(float64(target.ArmyQuantity) * 1.1)
		countOfSoldierCaptivedByWinner = int(float64(target.ArmyQuantity) * 0.2)
	} else {
		attackerWins = false
		countOfSoldierLoseOfWinner = int(float64(countOfSoldier) * 0.4)
		log.Println("countofsoldierdeath:", countOfSoldierLoseOfWinner)
		countOfSoldierCaptivedByWinner = int(float64(countOfSoldier) * 0.2)
		log.Println("captive:", countOfSoldierCaptivedByWinner)
	}

	return newFight(attacker, target, countOfSoldier, goldCost, attackerWins, countOfSoldierLoseOfWinner, countOfSoldierCaptivedByWinner)
}
