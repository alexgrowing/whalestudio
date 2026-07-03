package db

import (
	"time"

	"gopkg.in/mgo.v2/bson"
)

const (
	RoundTableName = "round"
)

type Round struct {
	Id      bson.ObjectId `bson:"_id"`
	When    time.Time
	RoomID  string
	Players []string
}
