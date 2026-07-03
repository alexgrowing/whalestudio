package db

import (
	"time"

	"gopkg.in/mgo.v2/bson"
	"ws/base"
)

const (
	SummaryTableName = "summary"
)

type Summary struct {
	Id                  bson.ObjectId `bson:"_id"`
	When                time.Time
	CountOfPublicRooms  int
	CountOfPrivateRooms int
	CountOfRingRooms    int
	CountOfRealPlayers  int
}

func newBlankSummary() *Summary {
	ret := Summary{}
	return &ret
}

func newSummary(countOfPublicRooms int, countOfPrivateRooms int, countOfRingRooms int, countOfRealPlayers int) *Summary {
	ret := Summary{}

	ret.Id = bson.NewObjectId()
	ret.When = time.Now()
	ret.CountOfPublicRooms = countOfPublicRooms
	ret.CountOfPrivateRooms = countOfPrivateRooms
	ret.CountOfRingRooms = countOfRingRooms
	ret.CountOfRealPlayers = countOfRealPlayers

	return &ret
}

func InsertSummary(countOfPublicRooms int, countOfPrivateRooms int, countOfRingRooms int, countOfRealPlayers int) {
	summary := newSummary(countOfPublicRooms, countOfPrivateRooms, countOfRingRooms, countOfRealPlayers)
	base.DBInsert(dbName, SummaryTableName, summary)
}

func LatestRoomInfo() (*Summary, error) {
	s, c := base.DBCollection(dbName, SummaryTableName)
	defer s.Close()

	summary := newBlankSummary()
	err := c.Find(nil).Sort("-when").One(summary)
	return summary, err
}
