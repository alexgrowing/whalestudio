package ws

import (
	"fmt"
	"time"
)

type _GameState struct {
	room                *Room
	beanEater           *_BeanEater
	currentXOfBeanEater int
	currentYOfBeanEater int
	countOfActionsLeft  int
}

// Start Start
func Start() {
	var players = &_BeanEaterPlayers{}
	for i := 0; i < len(players); i++ {
		players[i] = newBeanEaterRandom()
	}

	players.startGeneration(0)

	for i := uint(1); i <= countOfGeneration; i++ {
		players = players.nextGeneration()
		players.startGeneration(i)
	}
}

// OnePlayerStart OnePlayerStart
func OnePlayerStart(str string) {
	player := newBeanEaterByStrategy(str)

	var scoreOfRounds [countOfRounds]int
	for i := 0; i < countOfRounds; i++ {
		currentScore := player.currentPoint
		room := newRoom(50)
		countOfAllActions := 200
		if i == 0 {
			startGame(room, player, countOfAllActions, true)
		} else {
			startGame(room, player, countOfAllActions, false)
		}

		scoreOfRounds[i] = player.currentPoint - currentScore
	}

	max := -1000
	min := 1000
	for i := 0; i < len(scoreOfRounds); i++ {
		if max < scoreOfRounds[i] {
			max = scoreOfRounds[i]
		}
		if min > scoreOfRounds[i] {
			min = scoreOfRounds[i]
		}
	}

	fmt.Printf("max:%4d;min:%4d;avg:%4d\n", max, min, player.currentPoint/countOfRounds)
}

const countOfGeneration = 1000

func startGame(room *Room, eater *_BeanEater, countOfAllActions int, debug bool) {
	game := &_GameState{
		room:                room.clone(),
		beanEater:           eater,
		currentXOfBeanEater: 0,
		currentYOfBeanEater: 0,
		countOfActionsLeft:  countOfAllActions,
	}

	for game.countOfActionsLeft > 0 {
		if debug {
			game.draw()
		}
		game.action()
	}
	if debug {
		game.draw()
	}
}

func (me *_GameState) action() {
	idOfState := me.room.state(me.currentXOfBeanEater, me.currentYOfBeanEater).idOfStateOfPosition()
	actionOfState := me.beanEater.strategy[idOfState]

	newX2Try := me.currentXOfBeanEater
	newY2Try := me.currentYOfBeanEater

	if actionOfState == _ActionMoveRandom {
		actionOfState = createRandomMove()
	}

	switch actionOfState {
	case _ActionMoveUp:
		newX2Try = newX2Try - 1
		break
	case _ActionMoveDown:
		newX2Try = newX2Try + 1
		break
	case _ActionMoveLeft:
		newY2Try = newY2Try - 1
		break
	case _ActionMoveRight:
		newY2Try = newY2Try + 1
		break
	case _ActionEat:
		if me.room.spaces[me.currentXOfBeanEater][me.currentYOfBeanEater] {
			me.beanEater.currentPoint += 10
			me.room.spaces[me.currentXOfBeanEater][me.currentYOfBeanEater] = false
		} else {
			me.beanEater.currentPoint = me.beanEater.currentPoint - 1
		}
		break
	case _ActionNone:
		break
	}

	if me.tryMove2NewPosition(newX2Try, newY2Try) {
		me.currentXOfBeanEater = newX2Try
		me.currentYOfBeanEater = newY2Try
	} else {
		me.beanEater.currentPoint = me.beanEater.currentPoint - 5
	}

	me.countOfActionsLeft = me.countOfActionsLeft - 1
}

func (me *_GameState) tryMove2NewPosition(newX int, newY int) bool {
	if newX < 0 || newY < 0 || newX >= lengthOfSide || newY >= lengthOfSide {
		return false
	}

	return true
}

func (me *_GameState) draw() {
	time.Sleep(time.Duration(500) * time.Millisecond)
	for x := 0; x < lengthOfSide; x++ {
		for y := 0; y < lengthOfSide; y++ {
			if me.room.spaces[x][y] {
				print("1")
			} else {
				print("0")
			}
			if me.currentXOfBeanEater == x && me.currentYOfBeanEater == y {
				print("☠")
			}
			print("\t")
		}
		print("\n")
	}
	print(me.countOfActionsLeft, "------------------------------------\n")
}
