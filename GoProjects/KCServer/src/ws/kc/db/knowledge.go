package db

import (
	"gopkg.in/mgo.v2/bson"
	"time"
	"ws/base"
)

const (
	tableNameKnowledge = "Knowledge"
)

type IDBKnowledge interface {
	createAndSave2DB(json base.SM) (bson.ObjectId, error)
	readFromDBJson(json base.SM)
	encodeAsJson(json base.SM)

	markAsDeleted()
}

type DBKnowledge struct {
	UUID string
	Created time.Time
	Comments []string

	Deleted bool
}

func (self *DBKnowledge) decode(json base.SM) {
	self.UUID = json["uuid"].(string)
	self.Created = time.Unix(int64(json["created"].(float64)), 0)
	commentObs := json["comments"].([]interface{})
	self.Comments = make([]string, len(commentObs))
	for index, interf := range commentObs {
		self.Comments[index] = interf.(string)
	}

	self.Deleted = false
}

func (self *DBKnowledge) decodeFromDBJson(json base.SM) {
	self.UUID = json["uuid"].(string)
	self.Created = json["created"].(time.Time)
	commentObs := json["comments"].([]interface{})
	self.Comments = make([]string, len(commentObs))
	for index, interf := range commentObs {
		self.Comments[index] = interf.(string)
	}

	self.Deleted = json["deleted"].(bool)
}

func (self *DBKnowledge) encodeAsJson(json base.SM) {
	json["uuid"] = self.UUID
	json["created"] = self.Created.Unix()
	json["comments"] = self.Comments
}

type DBTextKnowledge struct {
	DBKnowledge

	Id   bson.ObjectId `bson:"_id"`
	Text string
}

func (self *DBTextKnowledge) createAndSave2DB(json base.SM) (bson.ObjectId, error) {
	self.DBKnowledge.decode(json)

	self.Text = json["text"].(string)
	self.Id = bson.NewObjectId()

	err := base.DBInsert(dbName, tableNameKnowledge, self)

	return self.Id, err
}

func (self *DBTextKnowledge) readFromDBJson(json base.SM) {
	self.DBKnowledge.decodeFromDBJson(json["dbknowledge"].(base.SM))
	self.Text = json["text"].(string)
	self.Id = json["_id"].(bson.ObjectId)
}

func (self *DBTextKnowledge) encodeAsJson(json base.SM) {
	self.DBKnowledge.encodeAsJson(json)

	json["text"] = self.Text
}

func (self *DBTextKnowledge) markAsDeleted() {
	self.Deleted = true
}

type DBImageKnowledge struct {
	DBKnowledge

	Id   bson.ObjectId `bson:"_id"`
	Filename string
}

func (self *DBImageKnowledge) createAndSave2DB(json base.SM) (bson.ObjectId, error) {
	self.DBKnowledge.decode(json)

	self.Filename = json["filename"].(string)
	self.Id = bson.NewObjectId()

	err := base.DBInsert(dbName, tableNameKnowledge, self)

	return self.Id, err
}

func (self *DBImageKnowledge) readFromDBJson(json base.SM) {
	self.DBKnowledge.decodeFromDBJson(json["dbknowledge"].(base.SM))
	self.Filename = json["filename"].(string)
	self.Id = json["_id"].(bson.ObjectId)
}

func (self *DBImageKnowledge) encodeAsJson(json base.SM) {
	self.DBKnowledge.encodeAsJson(json)

	json["filename"] = self.Filename
}

func (self *DBImageKnowledge) markAsDeleted() {
	self.Deleted = true
}

func UploadKnowledge(accountId bson.ObjectId, json base.SM) (time.Time, error) {
	var kc IDBKnowledge
	if json["text"] != nil {
		kc = interface{}(&DBTextKnowledge{}).(IDBKnowledge)
	} else {
		kc = interface{}(&DBImageKnowledge{}).(IDBKnowledge)
	}

	if idOfKnow, err := kc.createAndSave2DB(json); err == nil {
		return appendKnowlegeByAccountId(accountId, idOfKnow), nil
	} else {
		return time.Unix(0,0), err
	}
}

func EncodeKnowsAsJson(knows []IDBKnowledge) []base.SM {
	jsons := make([]base.SM, len(knows))
	for index, know := range knows {
		jsons[index] = base.SM{}
		know.encodeAsJson(jsons[index])
	}

	return jsons
}

func findKnowsById(idOfKnows []bson.ObjectId) ([]IDBKnowledge, error) {
	var allDBJson []base.SM

	err := base.DBFindAll(dbName, tableNameKnowledge, bson.M{"_id":bson.M{"$in":idOfKnows}}, &allDBJson)

	allKnows := make([]IDBKnowledge, len(allDBJson))
	for index, dbJson := range allDBJson {
		allKnows[index] = createKnowFromDBJson(dbJson)
	}

	return allKnows, err
}

func findOneKnowById(idOfKnow bson.ObjectId) (IDBKnowledge, error) {
	var json base.SM

	err := base.DBFindOne(dbName, tableNameKnowledge, bson.M{"_id":idOfKnow}, &json)

	return createKnowFromDBJson(json), err
}

func markKnowAsDeletedById(idOfKnow bson.ObjectId) {
	if know, err := findOneKnowById(idOfKnow); err == nil {
		know.markAsDeleted()

		base.DBUpdate(dbName, tableNameKnowledge, idOfKnow, know)
	}
}

func editKnowById(idOfKnow bson.ObjectId, newText string) {
	if know, err := findOneKnowById(idOfKnow); err == nil {
		if textKnow, ok := know.(*DBTextKnowledge); ok {
			textKnow.Text = newText

			base.DBUpdate(dbName, tableNameKnowledge, idOfKnow, textKnow)
		}
	}
}

func createKnowFromDBJson(json base.SM) IDBKnowledge {
	var know IDBKnowledge
	if json["text"] != nil {
		know = &DBTextKnowledge{}
	} else {
		know = &DBImageKnowledge{}
	}

	know.readFromDBJson(json)

	return know
}