package db

import (
	"time"

	"gopkg.in/mgo.v2/bson"
	"ws/base"
)

const (
	intoPrivateRoomTableName = "intoprivateroom"
)

type IntoPrivateRoom struct {
	Id               bson.ObjectId `bson:"_id"`
	UUID             string
	When             time.Time
}

func InsertIntoPrivateRoom(playerUUID string) error {
	into := IntoPrivateRoom{}
	into.Id = bson.NewObjectId()
	into.UUID = playerUUID
	into.When = time.Now()

	return base.DBInsert(dbName, intoPrivateRoomTableName, &into)
}

func PrivateRoomIn48Hours() int {
	if count, err := base.DBCount(dbName, intoPrivateRoomTableName, bson.M{"when": bsonOfRegionOf48Hours()}); err == nil {
		return count
	}

	return 0
}
