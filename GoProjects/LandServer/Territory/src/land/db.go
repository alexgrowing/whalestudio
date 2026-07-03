package land

import (
	"errors"
	"time"
	"tool"

	"gopkg.in/mgo.v2"
	"gopkg.in/mgo.v2/bson"
	"ws/base"
	"math"
)

const (
	DBConnection       = "mongodb://127.0.0.1/"
	DBName             = "Territory"
	AccountTableName   = "account"
	FootprintTableName = "footprint"
	StepTableName      = "step"
	TerritoryTableName = "territory"
	FightTableName     = "fight"

	DefaultUserName = "Robber"
)

func FindAccountByUUID(pid string) (*Account, error) {
	if len(pid) == 0 {
		return nil, errors.New("pid should not be empty")
	}

	if session, err := mgo.Dial(DBConnection); err == nil {
		defer session.Close()

		session.SetMode(mgo.Monotonic, true)

		c := session.DB(DBName).C(AccountTableName)
		accountFound := newBlankAccount()
		if err = c.Find(bson.M{"uuid": pid}).One(accountFound); err == nil {
			if accountFound.Training.CountOfSoldier > 0 && accountFound.isTrainingFinished() {
				accountFound.setTrainingFinished()
				err = UpdateAccountOnTrainingFinished(accountFound)
			}
		}

		return accountFound, err
	} else {
		return nil, err
	}
}

func InsertAccount(pid string, pname string) (*Account, error) {
	if session, err := mgo.Dial(DBConnection); err == nil {
		defer session.Close()

		session.SetMode(mgo.Monotonic, true)

		c := session.DB(DBName).C(AccountTableName)

		if len(pid) == 0 {
			pid = tool.GenerateUUID()
		}
		if len(pname) == 0 {
			pname = DefaultUserName
		}

		newAccount := newAccount(pid, pname)
		err = c.Insert(newAccount)

		return newAccount, err
	} else {
		return nil, err
	}
}

func UpdateLoginInformationOfAccount(account *Account) {
	loginLately := account.LoginLately
	now := time.Now()
	yesterday := now.AddDate(0, 0, -1)

	if loginLately.Year() == now.Year() && loginLately.Month() == now.Month() && loginLately.Day() == now.Day() {
		// 如果上次登录时间和当前是同一天
		account.LoginLately = now
	} else if loginLately.Year() == yesterday.Year() && loginLately.Month() == yesterday.Month() && loginLately.Day() == yesterday.Day() {
		// 如果上次登录时间和昨天是同一天
		account.LoginLately = now
		account.SummaryDaysOfLogin = account.SummaryDaysOfLogin + 1
		account.ContinuousDaysOfLoginLately = account.ContinuousDaysOfLoginLately + 1
	} else {
		// 如果上次登录时间是昨天以前
		account.LoginLately = now
		account.SummaryDaysOfLogin = account.SummaryDaysOfLogin + 1
		account.ContinuousDaysOfLoginLately = 1
	}

	if session, err := mgo.Dial(DBConnection); err == nil {
		defer session.Close()

		session.SetMode(mgo.Monotonic, true)

		c := session.DB(DBName).C(AccountTableName)

		c.UpdateId(account.Id, bson.M{"$set": bson.M{"loginlately": account.LoginLately, "summarydaysoflogin": account.SummaryDaysOfLogin, "continuousdaysofloginlately": account.ContinuousDaysOfLoginLately}})
	}
}

func UpdateNameOfAccount(account *Account) error {
	if session, err := mgo.Dial(DBConnection); err == nil {
		defer session.Close()

		session.SetMode(mgo.Monotonic, true)

		c := session.DB(DBName).C(AccountTableName)

		return c.UpdateId(account.Id, bson.M{"$set": bson.M{"name": account.Name, "free2rename": account.Free2Rename, "diamond": account.Diamond}})
	} else {
		return err
	}
}

func UpdateGoldOfAccount(account *Account) error {
	if session, err := mgo.Dial(DBConnection); err == nil {
		defer session.Close()

		session.SetMode(mgo.Monotonic, true)

		c := session.DB(DBName).C(AccountTableName)

		return c.UpdateId(account.Id, bson.M{"$set": bson.M{"gold": account.Gold}})
	} else {
		return err
	}
}

func UpdateDiamondOfAccount(account *Account) error {
	if session, err := mgo.Dial(DBConnection); err == nil {
		defer session.Close()

		session.SetMode(mgo.Monotonic, true)

		c := session.DB(DBName).C(AccountTableName)

		return c.UpdateId(account.Id, bson.M{"$set": bson.M{"diamond": account.Diamond}})
	} else {
		return err
	}
}

func UpdateAccountAfterAttack(account *Account) error {
	if session, err := mgo.Dial(DBConnection); err == nil {
		defer session.Close()

		session.SetMode(mgo.Monotonic, true)

		c := session.DB(DBName).C(AccountTableName)

		return c.UpdateId(account.Id, bson.M{"$set": bson.M{"armyquantity": account.ArmyQuantity}})
	} else {
		return err
	}
}

func UpdateAccountOnTrainingFinished(account *Account) error {
	if session, err := mgo.Dial(DBConnection); err == nil {
		defer session.Close()

		session.SetMode(mgo.Monotonic, true)

		c := session.DB(DBName).C(AccountTableName)

		return c.UpdateId(account.Id, bson.M{"$set": bson.M{"training": account.Training, "armyquantity": account.ArmyQuantity, "diamond": account.Diamond}})
	} else {
		return err
	}
}

func UpdateAccountAfterRecruit(account *Account) error {
	if session, err := mgo.Dial(DBConnection); err == nil {
		defer session.Close()

		session.SetMode(mgo.Monotonic, true)

		c := session.DB(DBName).C(AccountTableName)

		return c.UpdateId(account.Id, bson.M{"$set": bson.M{"gold": account.Gold, "training": account.Training}})
	} else {
		return err
	}
}

func UpdateAccountAfterGover(account *Account) error {
	if session, err := mgo.Dial(DBConnection); err == nil {
		defer session.Close()

		session.SetMode(mgo.Monotonic, true)

		c := session.DB(DBName).C(AccountTableName)

		return c.UpdateId(account.Id, bson.M{"$set": bson.M{"armyquantity": account.ArmyQuantity}})
	} else {
		return err
	}
}

func UpdateAccountOfIncreaseGoldByUUID(uuid string, gold2Increase int) error {
	if session, err := mgo.Dial(DBConnection); err == nil {
		defer session.Close()

		session.SetMode(mgo.Monotonic, true)

		c := session.DB(DBName).C(AccountTableName)

		return c.Update(bson.M{"uuid": uuid}, bson.M{"$inc": bson.M{"gold": gold2Increase}})
	} else {
		return err
	}
}

func FindFootprintsByUUID(pid string) ([]Footprint, error) {
	if session, err := mgo.Dial(DBConnection); err == nil {
		defer session.Close()

		session.SetMode(mgo.Monotonic, true)
		var footprints []Footprint
		c := session.DB(DBName).C(FootprintTableName)
		err = c.Find(bson.M{"accountuuid": pid}).All(&footprints)

		return footprints, err

	} else {
		return nil, err
	}
}

func InsertFootprint(fp *Footprint) error {
	if session, err := mgo.Dial(DBConnection); err == nil {
		defer session.Close()

		session.SetMode(mgo.Monotonic, true)

		c := session.DB(DBName).C(FootprintTableName)

		return c.Insert(fp)
	} else {
		return err
	}
}

func FindLastStepUploadedByUUID(pid string) (*Step, error) {
	if session, err := mgo.Dial(DBConnection); err == nil {
		defer session.Close()

		session.SetMode(mgo.Monotonic, true)

		c := session.DB(DBName).C(StepTableName)
		lastStepUploaded := newBlankStep()
		err = c.Find(bson.M{"accountuuid": pid}).Sort("-uploadtime").One(lastStepUploaded)

		return lastStepUploaded, err
	} else {
		return nil, err
	}
}

func UpdateStepOfNewCount(step *Step) error {
	if session, err := mgo.Dial(DBConnection); err == nil {
		defer session.Close()

		session.SetMode(mgo.Monotonic, true)

		c := session.DB(DBName).C(StepTableName)

		return c.UpdateId(step.Id, bson.M{"$set": bson.M{"uploadtime": time.Now(), "count": step.Count}})
	} else {
		return err
	}
}

func InsertStep(playerID string, count int) (*Step, error) {
	if session, err := mgo.Dial(DBConnection); err == nil {
		defer session.Close()

		session.SetMode(mgo.Monotonic, true)

		c := session.DB(DBName).C(StepTableName)

		newStep := newStep(playerID, count)
		err = c.Insert(newStep)

		return newStep, err
	} else {
		return nil, err
	}
}

func InsertFight(fight *Fight) error {
	if session, err := mgo.Dial(DBConnection); err == nil {
		defer session.Close()

		session.SetMode(mgo.Monotonic, true)

		c := session.DB(DBName).C(FightTableName)
		return c.Insert(fight)
	} else {
		return err
	}
}

func CountFightsByUUIDSince(playerID string, since time.Time) (int, error) {
	sumCount := 0

	if session, err := mgo.Dial(DBConnection); err == nil {
		defer session.Close()

		session.SetMode(mgo.Monotonic, true)

		c := session.DB(DBName).C(FightTableName)

		if countAsAttacker, err := c.Find(bson.M{"attackeruuid": playerID, "occured": bson.M{"$gte": since}}).Count(); err == nil {
			sumCount = sumCount + countAsAttacker
		}
		if countAsDefender, err := c.Find(bson.M{"defenderuuid": playerID, "occured": bson.M{"$gte": since}}).Count(); err == nil {
			sumCount = sumCount + countAsDefender
		}
	} else {
		return 0, err
	}

	return sumCount, nil
}

func FindRecentFightByAttacker(attackerUUID string) ([]Fight, error) {
	if session, err := mgo.Dial(DBConnection); err == nil {
		defer session.Close()

		session.SetMode(mgo.Monotonic, true)

		c := session.DB(DBName).C(FightTableName)

		var fights []Fight
		err = c.Find(bson.M{"attackeruuid": attackerUUID, "occured": bsonOfRegionOf48Hours()}).All(&fights)

		return fights, err
	} else {
		return nil, err
	}
}

func FindRecentFightByDefender(defenderUUID string) ([]Fight, error) {
	if session, err := mgo.Dial(DBConnection); err == nil {
		defer session.Close()

		session.SetMode(mgo.Monotonic, true)

		c := session.DB(DBName).C(FightTableName)

		var fights []Fight
		err = c.Find(bson.M{"defenderuuid": defenderUUID, "occured": bsonOfRegionOf48Hours()}).All(&fights)

		return fights, err
	} else {
		return nil, err
	}
}

func FindTerritoryByCoordinate(latitude100 int, longitude100 int) (*Territory, error) {
	if session, err := mgo.Dial(DBConnection); err == nil {
		defer session.Close()

		session.SetMode(mgo.Monotonic, true)

		c := session.DB(DBName).C(TerritoryTableName)

		newTerritory := newBlankTerritory()
		if err = c.Find(bson.M{"latitude100": latitude100, "longitude100": longitude100}).One(newTerritory); err != nil {
			newTerritory = newWildTerritory(latitude100, longitude100)
			err = c.Insert(newTerritory)
		}

		return newTerritory, err
	} else {
		return nil, err
	}
}

func FindTerritoriesByOwnerUUID(ownerUUID string) ([]Territory, error) {
	if session, err := mgo.Dial(DBConnection); err == nil {
		defer session.Close()

		session.SetMode(mgo.Monotonic, true)

		c := session.DB(DBName).C(TerritoryTableName)
		var myTerritories []Territory
		err = c.Find(bson.M{"owneruuid": ownerUUID}).All(&myTerritories)

		return myTerritories, err
	} else {
		return nil, err
	}
}

func UpdateTerritoryAfterFight(territory *Territory) error {
	if session, err := mgo.Dial(DBConnection); err == nil {
		defer session.Close()

		session.SetMode(mgo.Monotonic, true)

		c := session.DB(DBName).C(TerritoryTableName)

		return c.UpdateId(territory.Id, bson.M{"$set": bson.M{"owneruuid": territory.OwnerUUID, "armyquantity": territory.ArmyQuantity}})
	} else {
		return err
	}
}

func UpdateTerritoryAfterGover(territory *Territory) error {
	if session, err := mgo.Dial(DBConnection); err == nil {
		defer session.Close()

		session.SetMode(mgo.Monotonic, true)

		c := session.DB(DBName).C(TerritoryTableName)

		return c.UpdateId(territory.Id, bson.M{"$set": bson.M{"name": territory.Name, "armyquantity": territory.ArmyQuantity}})
	} else {
		return err
	}
}

func UpdateAllTerritoryAsTreasureSearchable() error {
	if session, err := mgo.Dial(DBConnection); err == nil {
		defer session.Close()

		session.SetMode(mgo.Monotonic, true)

		c := session.DB(DBName).C(TerritoryTableName)

		_, err := c.UpdateAll(bson.M{}, bson.M{"$set": bson.M{"treasuresearchable": true}})
		return err
	} else {
		return err
	}
}

func UpdateTerritoryAsTreasureUnsearchable(territory *Territory) error {
	if session, err := mgo.Dial(DBConnection); err == nil {
		defer session.Close()

		session.SetMode(mgo.Monotonic, true)

		c := session.DB(DBName).C(TerritoryTableName)

		return c.UpdateId(territory.Id, bson.M{"$set": bson.M{"treasuresearchable": false}})
	} else {
		return err
	}
}

func UpdateTerritoryAfterSearch(territory *Territory) error {
	if session, err := mgo.Dial(DBConnection); err == nil {
		defer session.Close()

		session.SetMode(mgo.Monotonic, true)

		c := session.DB(DBName).C(TerritoryTableName)

		if territory.UnixOfLastActivated == 0 {
			territory.UnixOfLastActivated = time.Now().Unix()
		}
		if len(territory.OwnerUUID) > 0 {
			territory.OccupiedSoldierSeconds = (time.Now().Unix() - territory.UnixOfLastActivated) * int64(territory.ArmyQuantity)
			territory.UnixOfLastActivated = time.Now().Unix()
		}

		return c.UpdateId(territory.Id, bson.M{"$inc": bson.M{"timessearched": 1}, "$set": bson.M{"unixoflastactivated": territory.UnixOfLastActivated, "occupiedsoldierseconds": territory.OccupiedSoldierSeconds}})
	} else {
		return err
	}
}

func CalculateAchievementByPlayerID(pid string) base.SM {
	sm := base.SM{}
	if account, err := FindAccountByUUID(pid); err == nil {
		sm["Name"] = account.Name
	}

	if footprints, err := FindFootprintsByUUID(pid); err == nil {
		locations := make([]Location, len(footprints))
		for i := 0; i < len(footprints); i++ {
			locations[i] = footprints[i]
		}
		sm["Footprints"] = summaryOfLocations(locations)
	}

	if territories, err := FindTerritoriesByOwnerUUID(pid); err == nil {
		locations := make([]Location, len(territories))
		for i := 0; i < len(territories); i++ {
			locations[i] = territories[i]
		}
		sm["Territories"] = summaryOfLocations(locations)
	}

	return sm
}

func summaryOfLocations(locations []Location) base.SM {
	sm := base.SM{}
	count := len(locations)
	sm["Count"] = count

	size, partOfMatchedCountry, nameOfMatchedCountry := calculateSizeOfCountry(len(locations))
	sm["Size"] = size
	sm["NameOfMatchedCountry"] = nameOfMatchedCountry
	sm["PartOfMatchedCountry"] = partOfMatchedCountry

	longitudeSet := make(map[int]int)
	latitudeSet := make(map[int]int)
	minLongitude := math.MaxInt64
	maxLongitude := math.MinInt64
	minLatitude := math.MaxInt64
	maxLatitude := math.MinInt64
	for i := 0; i < len(locations); i++ {
		long := locations[i].GetLongitude100()
		lati := locations[i].GetLatitude100()

		if _, exist := longitudeSet[long]; !exist {
			longitudeSet[long] = 1
		}
		if _, exist := latitudeSet[lati]; !exist {
			latitudeSet[lati] = 1
		}
		if minLongitude > long {
			minLongitude = long
		}
		if maxLongitude < long {
			maxLongitude = long
		}
		if minLatitude > lati {
			minLatitude = lati
		}
		if maxLatitude < lati {
			maxLatitude = lati
		}
	}

	sm["CountOfLongitude"] = len(longitudeSet)
	sm["CountOfLatitude"] = len(latitudeSet)
	sm["MaxLongitude"] = float64(maxLongitude) / 100.0
	sm["MinLongitude"] = float64(minLongitude) / 100.0
	sm["MaxLatitude"] = float64(maxLatitude) / 100.0
	sm["MinLatitude"] = float64(minLatitude) / 100.0

	return sm
}

func calculateSizeOfCountry(countOfLocations int) (float64, float64, string) {
	var nameOfMatchedCountry string
	var partOfMatchedCountry float64

	size := float64(countOfLocations) * square_of_each_location

	count_of_all_countries := len(square_of_all_countries)
	for i := count_of_all_countries - 1; i >= 0;i-- {
		cas := square_of_all_countries[i]
		if cas.square * 10000 > size || i == 0 {
			nameOfMatchedCountry = cas.name
			partOfMatchedCountry = size / (cas.square * 10000)
			break
		}
	}

	return size, partOfMatchedCountry, nameOfMatchedCountry
}

var square_of_each_location = float64(510067866) / float64(36000 * 18000)

var square_of_all_countries = []CountryAndSquare {
	CountryAndSquare{"俄罗斯",1707.5},
	CountryAndSquare{"加拿大",997.1},
	CountryAndSquare{"中国",960.1},
	CountryAndSquare{"美国",936.4},
	CountryAndSquare{"巴西",854.7},
	CountryAndSquare{"澳大利亚",774.1},
	CountryAndSquare{"印度",328.8},
	CountryAndSquare{"阿根廷",278.0},
	CountryAndSquare{"哈萨克斯坦",271.7},
	CountryAndSquare{"苏丹",250.6},
	CountryAndSquare{"阿尔及利亚",238.2},
	CountryAndSquare{"刚果{金}",234.5},
	CountryAndSquare{"沙特阿拉伯",215.0},
	CountryAndSquare{"墨西哥",195.8},
	CountryAndSquare{"印度尼西亚",190.5},
	CountryAndSquare{"利比亚",176.0},
	CountryAndSquare{"伊朗",163.3},
	CountryAndSquare{"蒙古",156.7},
	CountryAndSquare{"秘鲁",128.5},
	CountryAndSquare{"乍得",128.4},
	CountryAndSquare{"尼日尔",126.7},
	CountryAndSquare{"安哥拉",124.7},
	CountryAndSquare{"马里",124.0},
	CountryAndSquare{"南非",122.1},
	CountryAndSquare{"哥伦比亚",113.9},
	CountryAndSquare{"埃塞俄比亚",110.4},
	CountryAndSquare{"玻利维亚",109.9},
	CountryAndSquare{"毛里塔尼亚",102.6},
	CountryAndSquare{"埃及",100.1},
	CountryAndSquare{"坦桑尼亚",94.5},
	CountryAndSquare{"尼日利亚",92.4},
	CountryAndSquare{"委内瑞拉",91.2},
	CountryAndSquare{"纳米比亚",82.4},
	CountryAndSquare{"莫桑比克",80.2},
	CountryAndSquare{"巴基斯坦",79.6},
	CountryAndSquare{"土耳其",77.5},
	CountryAndSquare{"智利",75.7},
	CountryAndSquare{"赞比亚",75.3},
	CountryAndSquare{"缅甸",67.7},
	CountryAndSquare{"阿富汗",65.2},
	CountryAndSquare{"索马里",63.8},
	CountryAndSquare{"中非",62.3},
	CountryAndSquare{"乌克兰",60.4},
	CountryAndSquare{"马达加斯加",58.7},
	CountryAndSquare{"博茨瓦纳",58.2},
	CountryAndSquare{"肯尼亚",58.0},
	CountryAndSquare{"法国",55.2},
	CountryAndSquare{"也门",52.8},
	CountryAndSquare{"泰国",51.3},
	CountryAndSquare{"西班牙",50.6},
	CountryAndSquare{"土库曼斯坦",48.8},
	CountryAndSquare{"喀唛隆",47.5},
	CountryAndSquare{"巴布亚新几内亚",46.3},
	CountryAndSquare{"瑞典",45.0},
	CountryAndSquare{"乌兹别克斯坦",44.7},
	CountryAndSquare{"摩洛哥",44.7},
	CountryAndSquare{"伊拉克",43.8},
	CountryAndSquare{"巴拉圭",40.7},
	CountryAndSquare{"津巴布韦",39.1},
	CountryAndSquare{"日本",37.8},
	CountryAndSquare{"德国",35.7},
	CountryAndSquare{"刚果（布）",34.2},
	CountryAndSquare{"芬兰",33.8},
	CountryAndSquare{"越南",33.2},
	CountryAndSquare{"马来西亚",33.0},
	CountryAndSquare{"挪威",32.4},
	CountryAndSquare{"波兰",32.3},
	CountryAndSquare{"科特迪瓦",32.2},
	CountryAndSquare{"意大利",30.1},
	CountryAndSquare{"菲律宾",30.0},
	CountryAndSquare{"厄瓜多尔",28.4},
	CountryAndSquare{"布基纳法索",27.4},
	CountryAndSquare{"新西兰",27.1},
	CountryAndSquare{"加蓬",26.8},
	CountryAndSquare{"几内亚",24.6},
	CountryAndSquare{"英国",24.5},
	CountryAndSquare{"乌干达",24.1},
	CountryAndSquare{"加纳",23.9},
	CountryAndSquare{"罗马尼亚",23.8},
	CountryAndSquare{"老挝",23.7},
	CountryAndSquare{"圭亚那",21.5},
	CountryAndSquare{"阿曼",21.2},
	CountryAndSquare{"白俄罗斯",20.8},
	CountryAndSquare{"吉尔吉斯",19.9},
	CountryAndSquare{"塞内加尔",19.7},
	CountryAndSquare{"叙利亚",18.5},
	CountryAndSquare{"柬埔寨",18.1},
	CountryAndSquare{"乌拉圭",17.7},
	CountryAndSquare{"突尼斯",16.4},
	CountryAndSquare{"苏里南",16.3},
	CountryAndSquare{"尼泊尔",14.7},
	CountryAndSquare{"孟加拉",14.4},
	CountryAndSquare{"塔吉克斯坦",14.3},
	CountryAndSquare{"希腊",13.2},
	CountryAndSquare{"尼加拉瓜",13.0},
	CountryAndSquare{"朝鲜",12.1},
	CountryAndSquare{"马拉维",11.8},
	CountryAndSquare{"贝宁",11.3},
	CountryAndSquare{"洪都拉斯",11.2},
	CountryAndSquare{"利比里亚",11.1},
	CountryAndSquare{"古巴",11.1},
	CountryAndSquare{"保加利亚",11.1},
	CountryAndSquare{"危地马拉",10.9},
	CountryAndSquare{"冰岛",10.3},
	CountryAndSquare{"南斯拉夫",10.2},
	CountryAndSquare{"韩国",9.9},
	CountryAndSquare{"匈牙利",9.3},
	CountryAndSquare{"葡萄牙",9.2},
	CountryAndSquare{"约旦",8.9},
	CountryAndSquare{"阿塞拜疆",8.7},
	CountryAndSquare{"阿联酋",8.4},
	CountryAndSquare{"奥地利",8.4},
	CountryAndSquare{"捷克共和国",7.9},
	CountryAndSquare{"巴拿马",7.6},
	CountryAndSquare{"塞拉里昂",7.2},
	CountryAndSquare{"爱尔兰",7.0},
	CountryAndSquare{"格鲁吉亚",6.9},
	CountryAndSquare{"斯里兰卡",6.6},
	CountryAndSquare{"拉脱维亚",6.5},
	CountryAndSquare{"立陶宛",6.5},
	CountryAndSquare{"多哥",5.7},
	CountryAndSquare{"克罗地亚",5.7},
	CountryAndSquare{"哥斯达黎加",5.1},
	CountryAndSquare{"斯洛伐克",4.9},
	CountryAndSquare{"多米尼加",4.9},
	CountryAndSquare{"不丹",4.7},
	CountryAndSquare{"爱沙尼亚",4.5},
	CountryAndSquare{"丹麦",4.3},
	CountryAndSquare{"荷兰",4.1},
	CountryAndSquare{"瑞士",4.1},
	CountryAndSquare{"几内亚比绍",3.6},
	CountryAndSquare{"比利时-卢森堡",3.3},
	CountryAndSquare{"亚美尼亚",3.0},
	CountryAndSquare{"莱索托",3.0},
	CountryAndSquare{"阿尔巴尼亚",2.9},
	CountryAndSquare{"所罗门群岛",2.9},
	CountryAndSquare{"布隆迪",2.8},
	CountryAndSquare{"赤道几内亚",2.8},
	CountryAndSquare{"海地",2.8},
	CountryAndSquare{"卢旺达",2.6},
	CountryAndSquare{"吉布提",2.3},
	CountryAndSquare{"伯利兹",2.3},
	CountryAndSquare{"以色列",2.1},
	CountryAndSquare{"萨尔瓦多",2.1},
	CountryAndSquare{"斯洛文尼亚",2.0},
	CountryAndSquare{"新喀里多尼亚",1.9},
	CountryAndSquare{"科威特",1.8},
	CountryAndSquare{"斐济",1.8},
	CountryAndSquare{"斯威士兰",1.7},
	CountryAndSquare{"东帝汶",1.5},
	CountryAndSquare{"巴哈马",1.4},
	CountryAndSquare{"瓦努阿图",1.2},
	CountryAndSquare{"卡塔尔",1.1},
	CountryAndSquare{"冈比亚",1.1},
	CountryAndSquare{"牙买加",1.1},
	CountryAndSquare{"黎巴嫩",1.0},
	CountryAndSquare{"塞浦路斯",0.9},
	CountryAndSquare{"波多黎各",0.9},
	CountryAndSquare{"文莱",0.6},
	CountryAndSquare{"佛得角",0.4},
	CountryAndSquare{"萨摩亚",0.3},
	CountryAndSquare{"科摩罗",0.2},
	CountryAndSquare{"毛里求斯",0.2},
	CountryAndSquare{"香港",0.1},
	CountryAndSquare{"新加坡",0.1},
	CountryAndSquare{"塞舌尔",0.1},
	CountryAndSquare{"关岛",0.1},
	CountryAndSquare{"巴林",0.1},
	CountryAndSquare{"汤加",0.1},
	CountryAndSquare{"安提瓜和巴布达",0.04},
	CountryAndSquare{"巴巴多斯",0.04},
	CountryAndSquare{"格林纳达",0.03},
	CountryAndSquare{"马尔他",0.03},
}

type CountryAndSquare struct {
	name string
	square float64
}