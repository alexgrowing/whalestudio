package db

import (
	"gopkg.in/mgo.v2/bson"
	"ws/base"
)

const (
	tableNameTraining = "training"
)

type DBTraining struct {
	Id bson.ObjectId `bson:"_id"`

	IdOfAccount bson.ObjectId
	Date DBSimpleDate
	Moves []DBMove
	Feeling string
}

func (self *DBTraining) asSM() base.SM {
	smOfMoves := make([]base.SM, len(self.Moves))
	for i, m := range self.Moves {
		smOfMoves[i] = m.asSM()
	}

	sm := base.SM{
		"date":self.Date.asSM(),
		"moves": smOfMoves,
		"feeling" : self.Feeling,
	}

	return sm
}

func (self *DBTraining) isEmpty() bool {
	return len(self.Moves) == 0 && len(self.Feeling) == 0
}

func createNewTraining(accountId bson.ObjectId, json map[string]interface{}) *DBTraining {
	ob := DBTraining{}
	ob.Id = bson.NewObjectId()
	ob.IdOfAccount = accountId

	ob.Date = *createSimpleDate(json["date"].(map[string]interface{}))
	jsons4Moves := json["moves"].([]interface{})
	ob.Moves = make([]DBMove, len(jsons4Moves))
	for index, json4Move := range jsons4Moves {
		ob.Moves[index] = *createMove(json4Move.(map[string]interface{}))
	}
	ob.Feeling = json["feeling"].(string)

	return &ob
}

func SetNewTraining(accountId bson.ObjectId, json map[string]interface{}) {
	newTraining := createNewTraining(accountId, json)

	if _, err := base.DBDelete(dbName, tableNameTraining, bson.M{"idofaccount":newTraining.IdOfAccount, "date":newTraining.Date.asSM()}); err == nil {
		if !newTraining.isEmpty() {
			base.DBInsert(dbName, tableNameTraining, newTraining)
		}
	}
}

type DBSimpleDate struct {
	Year int
	Month int
	Day int
}

func (self *DBSimpleDate) asSM() base.SM {
	return base.SM{
		"year":self.Year,
		"month":self.Month,
		"day":self.Day,
	}
}

func createSimpleDate(json map[string]interface{}) *DBSimpleDate {
	ob := DBSimpleDate{}
	ob.Year = int(json["year"].(float64))
	ob.Month = int(json["month"].(float64))
	ob.Day = int(json["day"].(float64))

	return &ob
}

type DBMove struct {
	Name string
	Weight int
	Times int
}

func (self *DBMove) asSM() base.SM {
	return base.SM{
		"name":self.Name,
		"weight":self.Weight,
		"times":self.Times,
	}
}

func createMove(json map[string]interface{}) *DBMove {
	ob := DBMove{}
	ob.Name = json["name"].(string)
	ob.Weight = int(json["weight"].(float64))
	ob.Times = int(json["times"].(float64))

	return &ob
}

func UploadAllTrainings(accountId bson.ObjectId, jsons []interface{}) {
	base.DBDelete(dbName, tableNameTraining, bson.M{"idofaccount":accountId})

	for _, jsonOb := range jsons {
		ob := createNewTraining(accountId, jsonOb.(map[string]interface{}))

		base.DBInsert(dbName, tableNameTraining, *ob)
	}
}

func DownloadAllTrainings(accountId bson.ObjectId) []base.SM {
	var trainings []DBTraining

	if err := base.DBFindAll(dbName, tableNameTraining, bson.M{"idofaccount":accountId}, &trainings); err == nil {
		sms := make([]base.SM, len(trainings))
		for index, t := range trainings {
			sms[index] = t.asSM()
		}

		return sms
	}

	return []base.SM{}
}