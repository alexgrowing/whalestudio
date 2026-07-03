package db

import (
	"gopkg.in/mgo.v2/bson"
	"time"
	"ws/base"
)

const (
	tableNameAction = "action"
)

type DBAction struct {
	Id   bson.ObjectId `bson:"_id"`

	IdOfAccount bson.ObjectId
	LastModified time.Time
}

func (self *DBAction) asSM() base.SM {
	return base.SM{
		"lastmodified":self.LastModified.Unix(),
	}
}

func UploadAllAction(accountId bson.ObjectId, json map[string]interface{}) {
	base.DBDelete(dbName, tableNameAction, bson.M{"idofaccount":accountId})

	ob := DBAction{}
	ob.Id = bson.NewObjectId()
	ob.IdOfAccount = accountId
	ob.LastModified = time.Unix(int64(json["lastmodified"].(float64)), 0)

	base.DBInsert(dbName, tableNameAction, ob)
}

func DownloadAction(accountId bson.ObjectId, sm base.SM) {
	action := DBAction{}
	if err := base.DBFindOne(dbName, tableNameAction, bson.M{"idofaccount":accountId}, &action); err == nil {
		sm["lastmodified"] = action.LastModified.Unix()
	}
}

func FetchLastModifiedAsUnix(accountId bson.ObjectId) int64 {
	action := DBAction{}

	if err := base.DBFindOne(dbName, tableNameAction, bson.M{"idofaccount":accountId}, &action); err == nil {
		return action.LastModified.Unix()
	} else {
		return 0
	}
}