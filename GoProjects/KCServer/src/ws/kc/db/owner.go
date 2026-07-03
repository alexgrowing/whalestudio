package db

import (
	"gopkg.in/mgo.v2/bson"
	"time"
	"ws/base"
)

const (
	tableNameOwner = "Owner"
)

type DBOwner struct {
	Id   bson.ObjectId `bson:"_id"`

	IdOfOwner bson.ObjectId
	LastModified time.Time
	IdOfKnowledges []bson.ObjectId
}

func newBlankOwner() *DBOwner {
	return &DBOwner{}
}

func newOwnerByAccountId(accountId bson.ObjectId) *DBOwner {
	owner := newBlankOwner()
	owner.Id = bson.NewObjectId()
	owner.IdOfOwner = accountId
	owner.LastModified = time.Unix(0, 0)

	return owner
}

func appendKnowlegeByAccountId(accountId bson.ObjectId, knowledgeId bson.ObjectId) time.Time {
	owner := newBlankOwner()

	if err := base.DBFindOne(dbName, tableNameOwner, bson.M{"idofowner" : accountId}, owner); err != nil {
		owner = newOwnerByAccountId(accountId)

		base.DBInsert(dbName, tableNameOwner, owner)
	}

	owner.IdOfKnowledges = append(owner.IdOfKnowledges, knowledgeId)
	owner.LastModified = time.Now()
	base.DBUpdate(dbName, tableNameOwner, owner.Id, owner)

	return owner.LastModified
}

func findOwnerByAccountId(accountId bson.ObjectId) (*DBOwner, error) {
	owner := DBOwner{}

	if err := base.DBFindOne(dbName, tableNameOwner, bson.M{"idofowner":accountId}, &owner); err == nil {
		return &owner, nil
	} else {
		return nil, err
	}
}

func FetchLastModified(accountId bson.ObjectId) time.Time {
	if owner, err := findOwnerByAccountId(accountId); err == nil {
		return owner.LastModified
	} else {
		return time.Unix(0,0)
	}
}

func DownloadAllKnows(accountId bson.ObjectId) ([]IDBKnowledge, time.Time, error) {
	if owner, err := findOwnerByAccountId(accountId); err == nil {
		if knows, err := findKnowsById(owner.IdOfKnowledges); err == nil {
			return knows, owner.LastModified, nil
		} else {
			return []IDBKnowledge{}, time.Unix(0,0), err
		}
	} else {
		return []IDBKnowledge{}, time.Unix(0,0), err
	}
}

func EditKnowledge(accountId bson.ObjectId, index int, newText string) (time.Time, error) {
	if owner, err := findOwnerByAccountId(accountId); err == nil {
		idOfKnow2Edit := owner.IdOfKnowledges[index]
		editKnowById(idOfKnow2Edit, newText)

		owner.LastModified = time.Now()
		base.DBUpdate(dbName, tableNameOwner, owner.Id, owner)

		return owner.LastModified, nil
	} else {
		return time.Unix(0,0), err
	}
}

func DeleteKnowledge(accountId bson.ObjectId, index int) (time.Time, error) {
	if owner, err := findOwnerByAccountId(accountId); err == nil {
		idOfKnow2Delete := owner.IdOfKnowledges[index]
		markKnowAsDeletedById(idOfKnow2Delete)

		owner.IdOfKnowledges = append(owner.IdOfKnowledges[:index], owner.IdOfKnowledges[index+1:]...)
		owner.LastModified = time.Now()

		base.DBUpdate(dbName, tableNameOwner, owner.Id, owner)

		return owner.LastModified, nil
	} else {
		return time.Unix(0,0), err
	}
}