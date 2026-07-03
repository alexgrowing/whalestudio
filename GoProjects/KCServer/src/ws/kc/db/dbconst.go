package db

import (
	"ws/base"
	"gopkg.in/mgo.v2/bson"
)

const (
	dbName ="Know"
)

func Info() base.SM {
	ret := base.SM{}

	ret["countofplayers"], _ = base.DBCount(dbName, tableNameOwner, bson.M{})
	ret["countofcards"], _ = base.DBCount(dbName, tableNameKnowledge, bson.M{})

	return ret
}