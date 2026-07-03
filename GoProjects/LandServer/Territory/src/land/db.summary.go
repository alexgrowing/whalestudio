package land

import (
	"log"
	"strconv"
	"time"

	"gopkg.in/mgo.v2"
	"gopkg.in/mgo.v2/bson"
	"ws/base"
)

func SummaryAccount() base.SM {
	ret := base.SM{}
	if session, err := mgo.Dial(DBConnection); err == nil {
		defer session.Close()

		session.SetMode(mgo.Monotonic, true)

		c := session.DB(DBName).C(AccountTableName)
		if count, err := c.Count(); err == nil {
			ret["总用户数"] = count
		}

		regionOfToday := bsonOfRegionOfToday()

		if count, err := c.Find(bson.M{"created": regionOfToday}).Count(); err == nil {
			ret["今日新玩家数"] = count
		}
		if count, err := c.Find(bson.M{"loginlately": regionOfToday}).Count(); err == nil {
			ret["今日玩家数"] = count
		}

		accountFound := newBlankAccount()
		if err = c.Find(bson.M{}).Sort("-loginlately").One(accountFound); err == nil {
			smOfAccountFound := base.SM{}
			smOfAccountFound["name"] = accountFound.Name
			smOfAccountFound["login"] = accountFound.LoginLately.String()
			ret["最近登录的玩家"] = smOfAccountFound
		}
	}

	return ret
}

func SummaryTerritory() base.SM {
	ret := base.SM{}
	if session, err := mgo.Dial(DBConnection); err == nil {
		defer session.Close()

		session.SetMode(mgo.Monotonic, true)

		c := session.DB(DBName).C(TerritoryTableName)

		if count, err := c.Count(); err == nil {
			ret["已探索地块数"] = count
		}
		if count, err := c.Find(bson.M{"owneruuid": bson.M{"$ne": ""}}).Count(); err == nil {
			ret["被占领地块数"] = count
		}

		regionOfToday := bsonOfRegionOfToday()
		if count, err := c.Find(bson.M{"born": regionOfToday}).Count(); err == nil {
			ret["今日新探索地块数"] = count
		}

		ret["领地榜"] = summaryTerritoryByOwner(c)
		ret["探索榜"] = summaryTerritoryByDate(c)
	}

	return ret
}

func summaryTerritoryByOwner(c *mgo.Collection) []base.SM {
	owners := make([]base.SM, 0)

	groupO := bson.M{"$group": bson.M{
		// "_id":   bson.M{"year": bson.M{"$year": "$born"}, "month": bson.M{"$month": "$born"}, "day": bson.M{"$dayOfMonth": "$born"}},
		"_id":   bson.M{"Owner": "$owneruuid"},
		"count": bson.M{"$sum": 1},
	}}
	sortO := bson.M{"$sort": bson.M{
		"count": -1,
	}}
	limitO := bson.M{"$limit": 10}
	pipeOperations := []bson.M{groupO, sortO, limitO}
	results := []bson.M{}
	if err := c.Pipe(pipeOperations).All(&results); err == nil {
		for _, rt := range results {
			uuidOfOwner := (rt["_id"].(bson.M))["Owner"].(string)
			countOfDipan := rt["count"]
			nameOfOwner := "蛮荒领主"
			if len(uuidOfOwner) > 0 {
				if account, err := FindAccountByUUID(uuidOfOwner); err == nil {
					nameOfOwner = account.Name
				}
			}
			owners = append(owners, base.SM{nameOfOwner: countOfDipan})
		}
	} else {
		log.Println("fuck:", err.Error())
	}

	return owners
}

func summaryTerritoryByDate(c *mgo.Collection) []base.SM {
	byDate := make([]base.SM, 0)

	matchO := bson.M{"$match": bson.M{"born": bson.M{"$exists": true}}}

	groupO := bson.M{"$group": bson.M{
		"_id":   bson.M{"year": bson.M{"$year": "$born"}, "month": bson.M{"$month": "$born"}, "day": bson.M{"$dayOfMonth": "$born"}},
		"count": bson.M{"$sum": 1},
	}}
	sortO := bson.M{"$sort": bson.M{
		"_id.year": -1,
	}}
	limitO := bson.M{"$limit": 10}
	pipeOperations := []bson.M{matchO, groupO, sortO, limitO}
	results := []bson.M{}
	if err := c.Pipe(pipeOperations).All(&results); err == nil {
		for _, rt := range results {
			groupByYear := (rt["_id"].(bson.M))["year"].(int)
			groupByMonth := (rt["_id"].(bson.M))["month"].(int)
			groupByDay := (rt["_id"].(bson.M))["day"].(int)

			groupByDate := strconv.Itoa(groupByYear) + "-" + strconv.Itoa(groupByMonth) + "-" + strconv.Itoa(groupByDay)
			countOfDipan := rt["count"]
			byDate = append(byDate, base.SM{groupByDate: countOfDipan})
		}
	} else {
		log.Println("fuck:", err.Error())
	}

	return byDate
}

func SummaryFight() base.SM {
	ret := base.SM{}

	if session, err := mgo.Dial(DBConnection); err == nil {
		defer session.Close()

		session.SetMode(mgo.Monotonic, true)

		c := session.DB(DBName).C(FightTableName)

		if count, err := c.Count(); err == nil {
			ret["总战斗次数"] = count
		}
		if count, err := c.Find(bson.M{"defenderuuid": bson.M{"$ne": ""}}).Count(); err == nil {
			ret["人类战斗次数"] = count
		}
		if count, err := c.Find(bson.M{"defenderuuid": bson.M{"$ne": ""}, "occured": bsonOfRegionOf48Hours()}).Count(); err == nil {
			ret["48小时内人类战斗次数"] = count
		}
	}

	return ret
}

func bsonOfRegionOfToday() bson.M {
	now := time.Now()
	firstSecondTimeOfToday := time.Date(now.Year(), now.Month(), now.Day(), 0, 0, 0, 0, now.Location())
	return bson.M{"$gte": firstSecondTimeOfToday, "$lte": now}
}

func bsonOfRegionOf48Hours() bson.M {
	now := time.Now()
	timeOf48HoursAgo := now.AddDate(0, 0, -2)
	return bson.M{"$gte": timeOf48HoursAgo, "$lte": now}
}
