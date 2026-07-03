package base

import (
	"gopkg.in/mgo.v2"
	"gopkg.in/mgo.v2/bson"
)

const (
	dbConnection = "mongodb://127.0.0.1/"
)

var globalSession = singletonSession()

func singletonSession() *mgo.Session {
	s, _ := mgo.Dial(dbConnection)
	s.SetMode(mgo.Monotonic, true)

	return s
}

func EnsureIndex(dbName string, tableName string, index *mgo.Index) error {
	session := globalSession.Copy()
	defer session.Close()

	c:=session.DB(dbName).C(tableName)
	return c.EnsureIndex(*index)
}

func DBCollection(dbName string, tableName string) (*mgo.Session, *mgo.Collection) {
	session := globalSession.Copy()

	return session, session.DB(dbName).C(tableName)
}

func DBInsert(dbName string, tableName string, ob interface{}) error {
	session := globalSession.Copy()
	defer session.Close()

	c := session.DB(dbName).C(tableName)

	return c.Insert(ob)
}

func DBCount(dbName string, tableName string, m bson.M) (int, error) {
	session := globalSession.Copy()
	defer session.Close()

	c := session.DB(dbName).C(tableName)

	return c.Find(m).Count()
}

func DBDelete(dbName string, tableName string, m bson.M) (int, error) {
	session := globalSession.Copy()
	defer session.Close()

	c := session.DB(dbName).C(tableName)

	ci, err := c.RemoveAll(m)

	return ci.Removed, err
}

func DBFindOne(dbName string, tableName string, m bson.M, ob interface{}) error {
	session := globalSession.Copy()
	defer session.Close()

	c := session.DB(dbName).C(tableName)

	return c.Find(m).One(ob)
}

func DBFindAll(dbName string, tableName string, m bson.M, obs interface{}) error {
	session := globalSession.Copy()
	defer session.Close()

	c := session.DB(dbName).C(tableName)

	return c.Find(m).All(obs)
}

func DBUpdate(dbName string, tableName string, id bson.ObjectId, ob interface{}) error {
	session := globalSession.Copy()
	defer session.Close()

	c := session.DB(dbName).C(tableName)

	return c.UpdateId(id, ob)
}

func DBUpdateId(dbName string, tableName string, id bson.ObjectId, m bson.M) error {
	session := globalSession.Copy()
	defer session.Close()

	c := session.DB(dbName).C(tableName)

	return c.UpdateId(id, bson.M{"$set":m})
}

func DBUpdateBson(dbName string, tableName string, selector bson.M, modification bson.M) error {
	session := globalSession.Copy()
	defer session.Close()

	c := session.DB(dbName).C(tableName)

	return c.Update(selector, modification)
}