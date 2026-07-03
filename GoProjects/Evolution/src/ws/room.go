package ws

import (
	"bytes"
	"fmt"
	"math"
	"math/rand"
	"sort"
	"strconv"
	"strings"
)

const lengthOfSide = 10
const countOfAllKindsOfState = 3 * 3 * 3 * 3 * 3
const countOfPlayersEachGeneration = 200

type _SpaceType uint8

const (
	_SpaceTypeEmpty _SpaceType = 0
	_SpaceTypeBean  _SpaceType = 1
	_SpaceTypeWall  _SpaceType = 2
)

type _StateOfPosition struct {
	current _SpaceType
	up      _SpaceType
	down    _SpaceType
	left    _SpaceType
	right   _SpaceType
}

func (me *_StateOfPosition) idOfStateOfPosition() uint {
	return uint(me.current*1 + me.up*3 + me.down*9 + me.left*27 + me.right*81)
}

type _ActionType uint8

const (
	_ActionNone       _ActionType = 0
	_ActionMoveUp     _ActionType = 1
	_ActionMoveDown   _ActionType = 2
	_ActionMoveLeft   _ActionType = 3
	_ActionMoveRight  _ActionType = 4
	_ActionEat        _ActionType = 5
	_ActionMoveRandom _ActionType = 6
)

func createRandomActionType() _ActionType {
	return _ActionType(rand.Intn(7))
}

func createRandomMove() _ActionType {
	return _ActionType(rand.Intn(4) + 1)
}

type _Strategy [countOfAllKindsOfState]_ActionType

func (me *_Strategy) saveAsString() string {
	var buf bytes.Buffer
	for i := 0; i < len(me); i++ {
		if i > 0 {
			buf.WriteString(";")
		}
		buf.WriteString(strconv.Itoa(int(me[i])))
	}

	return buf.String()
}

func (me *_Strategy) readString(str string) {
	arr := strings.Split(str, ";")
	for i := 0; i < len(arr); i++ {
		if num, err := strconv.Atoi(arr[i]); err == nil {
			me[i] = _ActionType(num)
		}
	}
}

type _BeanEater struct {
	strategy     *_Strategy
	currentPoint int
}

func (me *_BeanEater) mutant() {
	for i := 0; i < len(me.strategy); i++ {
		if rand.Intn(200) == 0 { // 有两百分之一概率变异
			timesOfMutant++
			me.strategy[i] = createRandomActionType()
		}
	}
}

func newBeanEaterByStrategy(str string) *_BeanEater {
	eater := _BeanEater{
		currentPoint: 0,
	}

	newStrategy := &_Strategy{}
	newStrategy.readString(str)
	eater.strategy = newStrategy

	return &eater
}

func newBeanEaterRandom() *_BeanEater {
	eater := _BeanEater{
		currentPoint: 0,
		strategy:     &_Strategy{},
	}
	for i := 0; i < len(eater.strategy); i++ {
		eater.strategy[i] = createRandomActionType()
	}

	return &eater
}

type _BeanEaterPlayers [countOfPlayersEachGeneration]*_BeanEater

const countOfRounds = 1000

func (me *_BeanEaterPlayers) startGeneration(indexOfGeneration uint) {
	for i := 0; i < countOfRounds; i++ {
		me.startGameOfAllPlayers()
	}

	var max = -100000
	var indexOfMax = 0
	var min = 100000
	var sum = 0
	for i := 0; i < len(me); i++ {
		p := me[i].currentPoint / countOfRounds
		sum = sum + p
		if max < p {
			max = p
			indexOfMax = i
		}
		if min > p {
			min = p
		}
	}

	fmt.Printf("第%4d代\tmax:%4d;\tmin:%4d;\tavg:%4d;\tmutant:%d;\n", indexOfGeneration, max, min, sum/len(me), timesOfMutant)
	fmt.Println(me[indexOfMax].strategy.saveAsString())
	// for i := 0; i < len(countOfXYPicked); i++ {
	// 	print(countOfXYPicked[i])
	// 	if (i+1)%10 == 0 {
	// 		print("\n")
	// 	} else {
	// 		print("\t")
	// 	}
	// }
	// print("\n")
}

func (me *_BeanEaterPlayers) startGameOfAllPlayers() {
	room := newRoom(50)
	countOfAllActions := 200
	for i := 0; i < len(me); i++ {
		startGame(room, me[i], countOfAllActions, false)
	}
}

func (me *_BeanEaterPlayers) nextGeneration() *_BeanEaterPlayers {
	var newPlayers = &_BeanEaterPlayers{}
	sort.Sort(me)

	for i := 0; i < len(newPlayers); i = i + 2 {
		newPlayers[i], newPlayers[i+1] = me.pickRandomParents2BornChildren()
	}

	return newPlayers
}

func (me *_BeanEaterPlayers) pickRandomParents2BornChildren() (*_BeanEater, *_BeanEater) {
	x := array4RandomPick[rand.Intn(len(array4RandomPick))]
	countOfXYPicked[x]++
	y := x
	for y == x {
		y = array4RandomPick[rand.Intn(len(array4RandomPick))]
	}
	countOfXYPicked[y]++

	return createChildren(me[x], me[y])
}

func (me *_BeanEaterPlayers) Len() int {
	return len(me)
}

func (me *_BeanEaterPlayers) Swap(i, j int) {
	me[i], me[j] = me[j], me[i]
}

func (me *_BeanEaterPlayers) Less(i, j int) bool {
	return me[i].currentPoint < me[j].currentPoint
}

func initArray4RandomPick() []int {
	re := make([]int, 0)
	rate := math.Pow(100000, float64(1)/float64(countOfPlayersEachGeneration))
	for i := 0; i < countOfPlayersEachGeneration; i++ {
		countOfT := int(math.Pow(rate, float64(i)))
		// countOfT := i
		for ti := 0; ti < countOfT; ti++ {
			re = append(re, i)
		}
	}

	return re
}

var array4RandomPick = initArray4RandomPick()

var countOfXYPicked [countOfPlayersEachGeneration]int
var timesOfMutant int

func createChildren(papa *_BeanEater, mama *_BeanEater) (*_BeanEater, *_BeanEater) {
	cut := rand.Intn(countOfAllKindsOfState)

	var strategyOfBoy = &_Strategy{}
	var strategyOfGirl = &_Strategy{}

	for i := 0; i < countOfAllKindsOfState; i++ {
		if i < cut {
			strategyOfBoy[i] = papa.strategy[i]
			strategyOfGirl[i] = mama.strategy[i]
		} else {
			strategyOfBoy[i] = mama.strategy[i]
			strategyOfGirl[i] = papa.strategy[i]
		}
	}

	boy := &_BeanEater{
		strategy: strategyOfBoy,
	}
	boy.mutant()

	girl := &_BeanEater{
		strategy: strategyOfGirl,
	}
	girl.mutant()

	return boy, girl
}

// Room Room
type Room struct {
	spaces [lengthOfSide][lengthOfSide]bool
}

func newRoom(countOfBeans uint) *Room {
	room := Room{}

	for countOfBeans > 0 {
		randX := rand.Intn(lengthOfSide)
		randY := rand.Intn(lengthOfSide)

		if room.spaces[randX][randY] == false {
			room.spaces[randX][randY] = true
			countOfBeans--
		}
	}

	return &room
}

func (me *Room) state(x int, y int) *_StateOfPosition {
	return &_StateOfPosition{
		current: me.spaceTyepOfPosition(x, y),
		up:      me.spaceTyepOfPosition(x-1, y),
		down:    me.spaceTyepOfPosition(x+1, y),
		left:    me.spaceTyepOfPosition(x, y-1),
		right:   me.spaceTyepOfPosition(x, y+1),
	}
}

func (me *Room) clone() *Room {
	newRoom := Room{}
	for x := 0; x < lengthOfSide; x++ {
		for y := 0; y < lengthOfSide; y++ {
			newRoom.spaces[x][y] = me.spaces[x][y]
		}
	}

	return &newRoom
}

func (me *Room) spaceTyepOfPosition(x int, y int) _SpaceType {
	if x < 0 || y < 0 || x >= lengthOfSide || y >= lengthOfSide {
		return _SpaceTypeWall
	}

	if me.spaces[x][y] {
		return _SpaceTypeBean
	}

	return _SpaceTypeEmpty
}
