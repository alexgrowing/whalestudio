package land

import (
	"gopkg.in/mgo.v2"
	"gopkg.in/mgo.v2/bson"
)

func FindAllTerritories() ([]Territory, error) {
	if session, err := mgo.Dial(DBConnection); err == nil {
		defer session.Close()

		session.SetMode(mgo.Monotonic, true)

		c := session.DB(DBName).C(TerritoryTableName)

		var territories []Territory

		err := c.Find(bson.M{}).All(&territories)

		return territories, err
	} else {
		return nil, err
	}
}
