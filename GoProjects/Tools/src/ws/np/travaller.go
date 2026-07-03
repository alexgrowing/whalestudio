package np

import (
	"time"
	"math"
	"math/rand"
)

func StartTraveller() {
	countOfCordinates := 50
	allCordinates := make([]*Cordinate, countOfCordinates)
	for i:=0; i<50;i++ {
		allCordinates[i] = createCordinate(1000, 1000)
	}
}

func calcDistance(pointA *Cordinate, pointB *Cordinate) float64 {
	return math.Sqrt(math.Pow(math.Abs(float64(pointA.x - pointB.x)),2) + math.Pow(math.Abs(float64(pointA.y - pointB.y)),2))
}

type Cordinate struct {
	x int
	y int
}

func createCordinate(maxX int, maxY int) *Cordinate {
	rand.Seed(time.Now().UnixNano())

	return &Cordinate {
		x:rand.Intn(maxX),
		y:rand.Intn(maxY),
	}
}

