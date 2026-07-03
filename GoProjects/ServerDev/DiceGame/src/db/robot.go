package db

import (
	"errors"

	"gopkg.in/mgo.v2/bson"
	"ws/base"
)

const (
	robotTableName = "robot"
)

type Robot struct {
	Id        bson.ObjectId `bson:"_id"`
	NumberID  string
	Name      string
	Win       int
	Lose      int
	Attack    int
	Defend    int
	Crown     int
	Gold      int
	Available bool
}

func newBlankRobot() *Robot {
	return &Robot{}
}

func FindRobotByRandom(exceptions []string) (*Robot, error) {
	s, c := base.DBCollection(dbName, robotTableName)
	defer s.Close()

	query := c.Find(bson.M{"available": true})
	if countOfAllAvailableRobots, err := query.Count(); err == nil {
		if countOfAllAvailableRobots == 0 {
			return nil, errors.New("no available robots")
		}
		robot := newBlankRobot()

		err = query.Skip(base.CreateRandomInt(countOfAllAvailableRobots)).One(robot)

		for _, except := range exceptions {
			if robot.NumberID == except {
				return FindRobotByRandom(exceptions)
			}
		}

		return robot, err
	} else {
		return nil, err
	}
}

func UpdateRobotOnLoseByUUID(goldLost int, crownModification int, numberID string) error {
	return base.DBUpdateBson(dbName, robotTableName, bson.M{"numberid": numberID}, bson.M{"$inc": bson.M{"gold": -goldLost, "lose": 1, "crown": crownModification}})
}

func UpdateRobotOnWinByUUID(goldWin int, attackWin bool, currentDefendWins int, crownModification int, uuid string) error {
	var updateBson bson.M
	if attackWin {
		updateBson = bson.M{"$inc": bson.M{"gold": goldWin, "win": 1, "attack": 1, "crown": crownModification}}
	} else {
		updateBson = bson.M{"$inc": bson.M{"gold": goldWin, "win": 1, "crown": crownModification}}
	}
	return base.DBUpdateBson(dbName, robotTableName, bson.M{"numberid": uuid}, updateBson)
}

func UpdateRobotOnGoldGotByUUID(goldGot int, uuid string) error {
	return base.DBUpdateBson(dbName, robotTableName, bson.M{"numberid": uuid}, bson.M{"$inc": bson.M{"gold": goldGot}})
}
