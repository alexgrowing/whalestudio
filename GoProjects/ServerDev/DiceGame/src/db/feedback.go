package db

import (
	"time"

	"gopkg.in/mgo.v2/bson"
	"ws/base"
)

const (
	feedbackTableName = "feedback"
)

type Feedback struct {
	Id      bson.ObjectId `bson:"_id"`
	Name    string
	Content string
	When    time.Time
}

func FindRecent100Feedback() ([]Feedback, error) {
	var ret []Feedback

	s, c := base.DBCollection(dbName, feedbackTableName)
	defer s.Close()

	err := c.Find(nil).Sort("-when").Limit(100).All(&ret)
	return ret, err
}

func InsertFeedback(who string, content string) error {
	fb := Feedback{}

	fb.Id = bson.NewObjectId()
	fb.Name = who
	fb.Content = content
	fb.When = time.Now()

	return base.DBInsert(dbName, feedbackTableName, &fb)
}
