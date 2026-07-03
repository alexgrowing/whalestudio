package np

import (
	"math/rand"
	"strconv"
	"strings"
	"time"
	"github.com/deckarep/golang-set"
)

func StartSetCoverage() {
	var countOfAllStates = 10
	var countOfAllRadios = 10

	radios := make([]*Radio, countOfAllRadios)
	for i:=0; i < countOfAllRadios; i++ {
		radios[i]= createRadio(countOfAllStates)
	}

	var c uint64 = 0

	for i, radio := range radios {
		println(i,":",radio.toString())
		println(i,":",strconv.FormatUint(radio.statesCovered,2))
		c = c | radio.statesCovered
	}

	println(strconv.FormatUint(c,2))
	
	if (1 << uint64(countOfAllStates)) - 1 - c != 0 {
		panic("所有radio都无法覆盖所有states")
	}

	println("游戏正式开始...")

	c = 0
	radioSet := mapset.NewSetFromSlice(createRadioIndices(len(radios)))
	ps := radioSet.PowerSet()
	for radio := range ps.Iter() {
		c++
		println(c, ":", radio.(mapset.Set).Cardinality())
	}
}

func createRadioIndices(countOfRadios int) []interface{} {
	var radioIndices = make([]interface{}, countOfRadios)
	for i := 0; i < countOfRadios; i++ {
		radioIndices[i] = i
	}

	return radioIndices
}

type Radio struct {
	statesCovered uint64
}

func createRadio(countOfAllStates int) *Radio {
	var states uint64 = 0

	rand.Seed(time.Now().UnixNano())
	countOfStatesCovered := rand.Intn(10) + 1

	for i := 0; i < countOfStatesCovered; i++ {
		states = states | (1<<uint(rand.Intn(countOfAllStates)))
	}

	return &Radio{
		statesCovered: states,
	}
}

func (me *Radio) toString() string {
	array := make([]string, 0)
	i := uint64(0)
	for {
		c := uint64(1)<<i
		if c > me.statesCovered {
			break
		}
		if c & me.statesCovered > 0 {
			array = append(array, strconv.FormatUint(i, 10))
		}
		i++
	}
	                                                                                                 
	return strings.Join(array, ",")
}
