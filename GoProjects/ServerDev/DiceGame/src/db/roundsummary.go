package db

import (
	"time"

	"gopkg.in/mgo.v2/bson"

	"ws/base"
)

const (
	RoundSummaryTableName = "roundsummary"
)

type RoundSummary struct {
	Id           bson.ObjectId `bson:"_id"`
	When         time.Time
	CountOfHuman int
	CountOfRobot int
	RoomID       string
	TypeOfRoom   string
}

func newRoundSummary(countOfHuman int, countOfRobot int, roomID string, typeOfRoom string) *RoundSummary {
	ret := RoundSummary{}

	ret.Id = bson.NewObjectId()
	ret.When = time.Now()
	ret.CountOfHuman = countOfHuman
	ret.CountOfRobot = countOfRobot
	ret.RoomID = roomID
	ret.TypeOfRoom = typeOfRoom

	return &ret
}

/*
func FindRecent10RoundSummary() ([]RoundSummary, error) {
	ret := make([]RoundSummary, 0)

	if session, err := mgo.Dial(dbConnection); err == nil {
		defer session.Close()

		session.SetMode(mgo.Monotonic, true)

		c := session.DB(dbName).C(RoundSummaryTableName)
		err = c.Find(nil).Sort("-when").Limit(10).All(&ret)

		return ret, err
	} else {
		return ret, err
	}
}
*/

func RoundsInToday() base.SM {
	ret := base.SM{}

	if countOfRoundsIn48Hours, err := base.DBCount(dbName, RoundSummaryTableName, bson.M{"when": bsonOfRegionOfToday()}); err == nil {
		ret["总回合数"] = countOfRoundsIn48Hours
	}
	if countOfPublicRoundsIn48Hours, err := base.DBCount(dbName, RoundSummaryTableName, bson.M{"when": bsonOfRegionOfToday(), "typeofroom": "public"}); err == nil {
		ret["四人场"] = countOfPublicRoundsIn48Hours
	}
	if countOfPrivateRoundsIn48Hours, err := base.DBCount(dbName, RoundSummaryTableName, bson.M{"when": bsonOfRegionOfToday(), "typeofroom": "private"}); err == nil {
		ret["私密场"] = countOfPrivateRoundsIn48Hours
	}
	if countOfRingRoundsIn48Hours, err := base.DBCount(dbName, RoundSummaryTableName, bson.M{"when": bsonOfRegionOfToday(), "typeofroom": "ring"}); err == nil {
		ret["擂台赛"] = countOfRingRoundsIn48Hours
	}

	return ret
}

func RoundsIn48Hours() base.SM {
	ret := base.SM{}

	if countOfRoundsIn48Hours, err := base.DBCount(dbName, RoundSummaryTableName, bson.M{"when": bsonOfRegionOf48Hours()}); err == nil {
		ret["总回合数"] = countOfRoundsIn48Hours
	}
	if countOfPublicRoundsIn48Hours, err := base.DBCount(dbName, RoundSummaryTableName, bson.M{"when": bsonOfRegionOf48Hours(), "typeofroom": "public"}); err == nil {
		ret["四人场"] = countOfPublicRoundsIn48Hours
	}
	if countOfPrivateRoundsIn48Hours, err := base.DBCount(dbName, RoundSummaryTableName, bson.M{"when": bsonOfRegionOf48Hours(), "typeofroom": "private"}); err == nil {
		ret["私密场"] = countOfPrivateRoundsIn48Hours
	}
	if countOfRingRoundsIn48Hours, err := base.DBCount(dbName, RoundSummaryTableName, bson.M{"when": bsonOfRegionOf48Hours(), "typeofroom": "ring"}); err == nil {
		ret["擂台赛"] = countOfRingRoundsIn48Hours
	}

	return ret
}

func Recent10Rounds() []RoundSummary {
	ret := make([]RoundSummary, 0)

	s, c := base.DBCollection(dbName, RoundSummaryTableName)
	defer s.Close()

	blankSummary := RoundSummary{}
	iter := c.Find(bson.M{}).Sort("-when").Limit(10).Iter()
	for iter.Next(&blankSummary) {
		ret = append(ret, blankSummary)
	}

	return ret
}

/*
func CountByDateAndRoomType() ([]base.SM, error) {
	ret := make([]base.SM, 0)
	if session, err := mgo.Dial(dbConnection); err == nil {
		defer session.Close()

		session.SetMode(mgo.Monotonic, true)

		c := session.DB(dbName).C(RoundSummaryTableName)

		matchO := bson.M{"$match": bson.M{"when": bson.M{"$exists": true}}}
		groupO := bson.M{"$group": bson.M{
			"_id": bson.M{
				"year":     bson.M{"$year": "$when"},
				"month":    bson.M{"$month": "$when"},
				"day":      bson.M{"$dayOfMonth": "$when"},
				"roomtype": "$typeofroom",
			},
			"count": bson.M{"$sum": 1},
		}}
		sortO := bson.M{"$sort": bson.M{
			"_id.year":  -1,
			"_id.month": -1,
			"_id.day":   -1,
		}}
		limitO := bson.M{"$limit": 10}
		pipeOperations := []bson.M{matchO, groupO, sortO, limitO}

		results := []bson.M{}
		if err := c.Pipe(pipeOperations).All(&results); err == nil {
			for _, rt := range results {
				groupByYear := (rt["_id"].(bson.M))["year"].(int)
				groupByMonth := (rt["_id"].(bson.M))["month"].(int)
				groupByDay := (rt["_id"].(bson.M))["day"].(int)
				groupByType := (rt["_id"].(bson.M))["roomtype"].(string)

				groupByDate := strconv.Itoa(groupByYear) + "-" + strconv.Itoa(groupByMonth) + "-" + strconv.Itoa(groupByDay)
				countOfRooms := rt["count"].(int)
				ret = append(ret, base.SM{"日期": groupByDate, "房间类型": groupByType, "房间数量": countOfRooms})
			}

			return ret, nil
		} else {
			return ret, err
		}
	} else {
		return ret, err
	}
}
*/

func CountOfTypeOfPlayers() (int, int, error) {
	countOfAll, err := base.DBCount(dbName, RoundSummaryTableName, nil)
	countOfAllHumans, err := base.DBCount(dbName, RoundSummaryTableName,bson.M{"countofrobot": 0})
	return countOfAll, countOfAllHumans, err
}

func InsertRoundSummary(countOfHuman int, countOfRobot int, roomID string, typeOfRoom string) error {
	rs := newRoundSummary(countOfHuman, countOfRobot, roomID, typeOfRoom)

	return base.DBInsert(dbName, RoundSummaryTableName, rs)
}
