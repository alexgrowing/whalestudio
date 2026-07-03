package db

import (
	"time"

	"gopkg.in/mgo.v2/bson"
)

const (
	dbName       = "Dice"
)

func bsonOfRegionOf48Hours() bson.M {
	now := time.Now()
	timeOf48HoursAgo := now.AddDate(0, 0, -2)
	return bson.M{"$gte": timeOf48HoursAgo, "$lte": now}
}

func bsonOfRegionOfToday() bson.M {
	now := time.Now()
	firstSecondTimeOfToday := time.Date(now.Year(), now.Month(), now.Day(), 0, 0, 0, 0, now.Location())
	return bson.M{"$gte": firstSecondTimeOfToday, "$lte": now}
}

/*
func InsertTestRobots(w http.ResponseWriter, r *http.Request) {
	mgoSession, err := mgo.Dial(dbConnection)
	defer mgoSession.Close()
	if err != nil {
		return
	}
	mgoSession.SetMode(mgo.Monotonic, true)

	c := mgoSession.DB(dbName).C(robotTableName)
	c.Insert(newCustomRobot(1, "aaa"))
	c.Insert(newCustomRobot(2, "bbbbb"))
	c.Insert(newCustomRobot(3, "cccccc"))
	c.Insert(newCustomRobot(4, "ddddd"))
	c.Insert(newCustomRobot(5, "我是三厢"))
	c.Insert(newCustomRobot(6, "大运会"))
	c.Insert(newCustomRobot(7, "基"))
	c.Insert(newCustomRobot(8, "爱你老公"))
	c.Insert(newCustomRobot(9, "脸"))
	c.Insert(newCustomRobot(10, "瑶"))
	c.Insert(newCustomRobot(11, "真爱末年有"))
	c.Insert(newCustomRobot(12, "圾"))
	c.Insert(newCustomRobot(13, "来找我玩"))
	c.Insert(newCustomRobot(14, "来找我玩提"))
	c.Insert(newCustomRobot(15, "不打算"))
}

func newCustomRobot(numberID int, name string) *Robot {
	robot := Robot{}
	robot.Id = bson.NewObjectId()
	robot.Name = name
	robot.NumberID = strconv.Itoa(numberID)
	robot.Available = true
	robot.Win = 0
	robot.Lose = 0
	robot.Attack = 0
	robot.Defend = 0
	robot.Gold = 0

	return &robot
}
*/

/*
func Transfer(w http.ResponseWriter, r *http.Request) {
	var DB_URL = "root:123456@tcp(127.0.0.1:3306)/DICE?charset=utf8"
	mgoSession, err := mgo.Dial(dbConnection)
	if err != nil {
		return
	}
	mgoSession.SetMode(mgo.Monotonic, true)

	if db, err := sql.Open("mysql", DB_URL); err == nil {
		defer db.Close()

		if rows, err := db.Query("select uuid,name,win,lose,unix_timestamp(created),unix_timestamp(lastplay),attack,defend,gold from PLAYER"); err == nil {
			var (
				playerUUID string
				playerName string
				win        int
				lose       int
				created    int64
				lastplay   int64
				attack     int
				defend     int
				gold       int
			)

			c := mgoSession.DB(dbName).C(playerTableName)
			c.RemoveAll(nil)

			for rows.Next() {
				rows.Scan(&playerUUID, &playerName, &win, &lose, &created, &lastplay, &attack, &defend, &gold)

				p2Insert := Player{}
				p2Insert.Id = bson.NewObjectId()
				p2Insert.UUID = playerUUID
				p2Insert.Name = playerName
				p2Insert.Win = win
				p2Insert.Lose = lose
				p2Insert.Created = time.Unix(created, 0)
				p2Insert.LastPlay = time.Unix(lastplay, 0)
				p2Insert.Attack = attack
				p2Insert.Defend = defend
				p2Insert.Gold = gold

				c.Insert(p2Insert)
			}
		} else {
			fmt.Println(err.Error())
		}

		if rows, err := db.Query("select * from CARD"); err == nil {
			var (
				ownerUUID string
				cardType  string
				quantity  int
			)

			c := mgoSession.DB(dbName).C(cardTableName)
			c.RemoveAll(nil)

			for rows.Next() {
				rows.Scan(&ownerUUID, &cardType, &quantity)

				p2Insert := Card{}
				p2Insert.Id = bson.NewObjectId()
				p2Insert.OwnerUUID = ownerUUID
				p2Insert.TypeOfCard = cardType
				p2Insert.Quantity = quantity

				c.Insert(p2Insert)
			}
		} else {
			fmt.Println(err.Error())
		}

		if rows, err := db.Query("select user,typeofcard,unix_timestamp(when) from CARDUSAGE"); err == nil {
			var (
				user     string
				cardType string
				when     int64
			)

			c := mgoSession.DB(dbName).C(cardUsageTableName)
			c.RemoveAll(nil)

			for rows.Next() {
				rows.Scan(&user, &cardType, &when)

				p2Insert := CardUsage{}
				p2Insert.Id = bson.NewObjectId()
				p2Insert.UserUUID = user
				p2Insert.TypeOfCard = cardType
				p2Insert.When = time.Unix(when, 0)

				c.Insert(p2Insert)
			}
		} else {
			fmt.Println(err.Error())
		}

		if rows, err := db.Query("select name,content,unix_timestamp(time) from FEEDBACK"); err == nil {
			var (
				name    string
				content string
				when    int64
			)

			c := mgoSession.DB(dbName).C(feedbackTableName)
			c.RemoveAll(nil)

			for rows.Next() {
				rows.Scan(&name, &content, &when)

				p2Insert := Feedback{}
				p2Insert.Id = bson.NewObjectId()
				p2Insert.Name = name
				p2Insert.Content = content
				p2Insert.When = time.Unix(when, 0)

				c.Insert(p2Insert)
			}
		} else {
			fmt.Println(err.Error())
		}

		if rows, err := db.Query("select * from ROBOT"); err == nil {
			var (
				numberID  int
				name      string
				win       int
				lose      int
				available int
				attack    int
				defend    int
				gold      int
			)

			c := mgoSession.DB(dbName).C(robotTableName)
			c.RemoveAll(nil)

			for rows.Next() {
				rows.Scan(&numberID, &name, &win, &lose, &available, &attack, &defend, &gold)

				p2Insert := Robot{}
				p2Insert.Id = bson.NewObjectId()
				p2Insert.NumberID = strconv.Itoa(numberID)
				p2Insert.Name = name
				p2Insert.Win = win
				p2Insert.Lose = lose
				p2Insert.Available = (available == 1)
				p2Insert.Attack = attack
				p2Insert.Defend = defend
				p2Insert.Gold = gold

				c.Insert(p2Insert)
			}
		} else {
			fmt.Println(err.Error())
		}
	} else {
		fmt.Println(err.Error())
	}
}
*/
