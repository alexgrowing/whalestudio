package land

import (
	"encoding/json"
	"log"
	"math"
	"net/http"
	"strconv"
	"time"
	"ws/base"
)

var bundle_INAPP_PURCHASE_DIAMOND_50 = "diamond_50"

func DeprecatedHandler(w http.ResponseWriter, r *http.Request) {
	log.Println("deprecated")
	ret := base.SM{"deprecated": true}
	ret.Write(w)
}

func LoginHandler(w http.ResponseWriter, r *http.Request) {
	playerID := r.FormValue("pid")
	playerName := r.FormValue("pname")
	pprints := r.FormValue("prints")

	savedFootprints := make([]*SimpleFootprint, 0)
	var jsonPrintsArray []base.SM
	if err := json.Unmarshal([]byte(pprints), &jsonPrintsArray); err == nil {
		for ji := 0; ji < len(jsonPrintsArray); ji++ {
			newFP := newSimpleFootprintByJson(jsonPrintsArray[ji])
			savedFootprints = append(savedFootprints, newFP)
		}
	}

	ret := base.SM{}
	var accountReturn *Account
	jsonFootprints := make([]base.SM, 0)
	jsonMyTerritories := make([]base.SM, 0)

	if accountFound, err := FindAccountByUUID(playerID); err == nil {
		// 数据库里面有对应的account
		accountReturn = accountFound

		if footprintsFound, err := FindFootprintsByUUID(playerID); err == nil {
			for _, footprint := range footprintsFound {
				savedByClient := false
				// 客户端中已经保存了这个Footprint的话,就不需要再传给客户端了
				for _, savedFp := range savedFootprints {
					if savedFp.Latitude100 == footprint.Latitude100 && savedFp.Longitude100 == footprint.Longitude100 {
						savedByClient = true
						break
					}
				}

				if !savedByClient {
					jsonFootprints = append(jsonFootprints, footprint.writeAsJsonable())
				}
			}
		}

		if myTerritoriesFound, err := FindTerritoriesByOwnerUUID(playerID); err == nil {
			for _, territory := range myTerritoriesFound {
				jsonMyTerritories = append(jsonMyTerritories, territory.writeCoordinatAsJsonable())
			}
		}
	} else {
		if newAccount, err := InsertAccount(playerID, playerName); err == nil {
			accountReturn = newAccount
		} else {
			ret["error"] = err.Error()
		}
	}

	ret["footprints"] = jsonFootprints
	ret["myterritories"] = jsonMyTerritories

	if accountReturn != nil {
		ret["validuuid"] = accountReturn.UUID
		ret["validname"] = accountReturn.Name
		ret["countofgold"] = accountReturn.Gold
		ret["countofsoldier"] = accountReturn.ArmyQuantity
		ret["levelofsoldier"] = accountReturn.ArmyTrainingLevel
		ret["countofdiamond"] = accountReturn.Diamond
		ret["training"] = accountReturn.Training.writeAsJsonable()
		ret["free2rename"] = accountReturn.Free2Rename
	}

	UpdateLoginInformationOfAccount(accountReturn)

	ret.Write(w)
}

func RenameHandler(w http.ResponseWriter, r *http.Request) {
	playerID := r.FormValue("pid")
	playerName := r.FormValue("pname")

	if len(playerID) == 0 || len(playerName) == 0 {
		return
	}

	if accountFound, err := FindAccountByUUID(playerID); err == nil {
		if !accountFound.Free2Rename {
			if accountFound.Diamond >= PRICE_OF_DIAMOND_2_RENAME {
				accountFound.Diamond = accountFound.Diamond - PRICE_OF_DIAMOND_2_RENAME
			} else {
				ret := base.SM{"error": ERROR_CODE_NOT_ENOUGH_DIAMOND}
				ret.Write(w)
				return
			}
		}

		accountFound.Name = playerName
		accountFound.Free2Rename = false

		UpdateNameOfAccount(accountFound)

		ret := base.SM{"error": ERROR_NONE, "newname": playerName, "newdiamond": accountFound.Diamond}
		ret.Write(w)
	}
}

func PurchaseHandler(w http.ResponseWriter, r *http.Request) {
	playerID := r.FormValue("pid")
	bundleID := r.FormValue("bundle")
	if len(playerID) == 0 {
		return
	}

	if accountFound, err := FindAccountByUUID(playerID); err == nil {
		if bundleID == bundle_INAPP_PURCHASE_DIAMOND_50 {
			accountFound.Diamond = accountFound.Diamond + 50
			UpdateDiamondOfAccount(accountFound)

			ret := base.SM{"countofdiamondpurchased": 50}
			ret.Write(w)
		}
	}
}

func FootprintHandler(w http.ResponseWriter, r *http.Request) {
	pid := r.FormValue("pid")
	jsonStringOfFootprint := r.FormValue("fp")

	var jsonOb map[string]interface{}
	if err := json.Unmarshal([]byte(jsonStringOfFootprint), &jsonOb); err == nil {
		fp := newFootprintByJson(pid, jsonOb)

		if err = InsertFootprint(fp); err != nil {
			log.Println("error:", err, "\n\tinsert footprint:", fp)
		}
	} else {
		log.Println("error:", err, "\n\tjsondecode:", jsonStringOfFootprint)
	}
}

func StepHandler(w http.ResponseWriter, r *http.Request) {
	log.Println("step")

	pid := r.FormValue("pid")
	countString := r.FormValue("count")

	if len(pid) == 0 {
		return
	}
	countInt, err := strconv.Atoi(countString)
	if err != nil {
		log.Println(err)
		return
	}

	accountFound, err := FindAccountByUUID(pid)
	if err != nil {
		log.Println(err)
		return
	}

	uploadedToday := false
	stepDeltaToday := 0
	lastStepUploaded, err := FindLastStepUploadedByUUID(accountFound.UUID)
	if err == nil {
		// 找到了
		now := time.Now()
		yearOfToday, monthOfToday, dayOfToday := now.Date()
		if lastStepUploaded.UploadTime.After(time.Date(yearOfToday, monthOfToday, dayOfToday, 0, 0, 0, 0, time.Local)) {
			// 如果最后一次上传步数的时候是今天,那么Update
			uploadedToday = true
			stepDeltaToday = countInt - lastStepUploaded.Count
			if stepDeltaToday > 0 {
				lastStepUploaded.Count = countInt
				if err = UpdateStepOfNewCount(lastStepUploaded); err != nil {
					log.Println(err)
					return
				}
			}
		}
	}

	if !uploadedToday {
		if _, err := InsertStep(pid, countInt); err != nil {
			log.Println(err)
			return
		} else {
			stepDeltaToday = countInt
		}
	}

	if stepDeltaToday >= 0 {
		accountFound.Gold = accountFound.Gold + stepDeltaToday
		if err = UpdateGoldOfAccount(accountFound); err != nil {
			log.Println(err)
		} else {
			ret := base.SM{"gold": stepDeltaToday}
			ret.Write(w)
		}
	}
}

func RecruitSoldierHandler(w http.ResponseWriter, r *http.Request) {
	log.Println("recruit")

	pid := r.FormValue("pid")
	countString := r.FormValue("count")

	if len(pid) == 0 {
		return
	}
	countInt, err := strconv.Atoi(countString)
	if err != nil {
		log.Println(err)
		return
	}

	accountFound, err := FindAccountByUUID(pid)
	if err != nil {
		log.Println(err)
		return
	}

	if accountFound.Training.CountOfSoldier > 0 {
		return
	}

	goldCost := PRICE_OF_EACH_SOLDIER * countInt
	if accountFound.Gold >= goldCost {
		accountFound.Gold = accountFound.Gold - goldCost
		accountFound.Training = newTraining(countInt)

		if err = UpdateAccountAfterRecruit(accountFound); err == nil {
			ret := base.SM{
				"goldcost": goldCost,
				"training": accountFound.Training.writeAsJsonable(),
			}
			ret.Write(w)
		}
	}
}

func QuickFinishTrainingHandler(w http.ResponseWriter, r *http.Request) {
	log.Println("quickfinishtraining")

	pid := r.FormValue("pid")

	if len(pid) == 0 {
		return
	}

	accountFound, err := FindAccountByUUID(pid)
	if err != nil {
		log.Println(err)
		return
	}

	secondsLeft := accountFound.Training.End.Unix() - time.Now().Unix()
	if secondsLeft <= 0 {
		secondsLeft = 0
	}
	diamondCost := int(math.Ceil(float64(secondsLeft) / float64(COUNT_OF_SECONDS_PER_DIAMOND)))

	if accountFound.Diamond >= diamondCost {
		accountFound.setTrainingFinished()
		accountFound.Diamond = accountFound.Diamond - diamondCost

		UpdateAccountOnTrainingFinished(accountFound)

		ret := base.SM{
			"error":      ERROR_NONE,
			"newdiamond": accountFound.Diamond,
			"newsoldier": accountFound.ArmyQuantity,
		}
		ret.Write(w)
	} else {
		ret := base.SM{
			"error": ERROR_CODE_NOT_ENOUGH_DIAMOND,
		}
		ret.Write(w)
	}

	/*
		goldCost := PRICE_OF_EACH_SOLDIER * countInt
		if accountFound.Gold >= goldCost {
			accountFound.Gold = accountFound.Gold - goldCost
			accountFound.Training = newTraining(countInt)

			if err = UpdateAccountAfterRecruit(accountFound); err == nil {
				ret := base.SM{
					"goldcost": goldCost,
					"training": accountFound.Training.writeAsJsonable(),
				}
				ret.Write(w)
			}
		}
	*/
}

func AttackHandler(w http.ResponseWriter, r *http.Request) {
	log.Println("developing attack")

	pid := r.FormValue("pid")
	countOfSoldierString := r.FormValue("countofsoldier")
	latitudeString := r.FormValue("lat")
	longitudeString := r.FormValue("lon")

	if len(pid) == 0 {
		return
	}
	countOfSoldierInt, err := strconv.Atoi(countOfSoldierString)
	if err != nil {
		log.Println(err)
		return
	}
	latitudeInt, err := strconv.Atoi(latitudeString)
	if err != nil {
		log.Println(err)
		return
	}
	longitudeInt, err := strconv.Atoi(longitudeString)
	if err != nil {
		log.Println(err)
		return
	}

	accountFound, err := FindAccountByUUID(pid)
	if err != nil {
		log.Println(err)
		return
	}
	// 钱都不够,打毛仗
	goldCost := countOfSoldierInt * PRICE_OF_EACH_SOLDIER_2_CAMPAIGN
	if accountFound.Gold < goldCost {
		return
	}
	territoryFound, err := FindTerritoryByCoordinate(latitudeInt, longitudeInt)
	if err != nil {
		log.Println(err)
		return
	}

	fight := attack(accountFound, countOfSoldierInt, goldCost, territoryFound)
	if err = InsertFight(fight); err == nil {
		if fight.AttackerWins {
			// Territory的主人要改变,城防的士兵直接变成出征的士兵 - 死去的士兵 + 俘虏的士兵
			territoryFound.OwnerUUID = fight.AttackerUUID
			territoryFound.ArmyQuantity = fight.AttackerArmyQuantity - fight.QuantityLosesOfWinner + fight.QuantityCaptiveOfWinner
		} else {
			// 城防的士兵变成原来城防的士兵 - 死去的士兵 + 俘虏的士兵
			territoryFound.ArmyQuantity = fight.DefenderArmyQuantity - fight.QuantityLosesOfWinner + fight.QuantityCaptiveOfWinner
		}

		accountFound.ArmyQuantity = accountFound.ArmyQuantity - countOfSoldierInt
		if err = UpdateAccountAfterAttack(accountFound); err != nil {
			log.Println(err)
		}

		accountFound.Gold = accountFound.Gold - goldCost
		if err = UpdateGoldOfAccount(accountFound); err != nil {
			log.Println(err)
		}

		if err = UpdateTerritoryAfterFight(territoryFound); err == nil {
			fight.writeAsJsonable().Write(w)
		}
	}
}

func BriefFightsHandler(w http.ResponseWriter, r *http.Request) {
	log.Println("brief fights")

	playerID := r.FormValue("pid")

	ret := base.SM{}

	jsonAttacks := make([]base.SM, 0)
	jsonDefends := make([]base.SM, 0)

	if len(playerID) > 0 {
		if recentAttacksIStarted, err := FindRecentFightByAttacker(playerID); err == nil {
			for _, fight := range recentAttacksIStarted {
				jsonAttacks = append(jsonAttacks, fight.writeAsJsonable())
			}
		}
		if recentDefendsITook, err := FindRecentFightByDefender(playerID); err == nil {
			for _, fight := range recentDefendsITook {
				jsonDefends = append(jsonDefends, fight.writeAsJsonable())
			}
		}
	}

	ret["asattacker"] = jsonAttacks
	ret["asdefender"] = jsonDefends

	ret.Write(w)
}

func FetchCountOfNewFightsHandler(w http.ResponseWriter, r *http.Request) {
	log.Println("fetch count of new fights")

	playerID := r.FormValue("pid")
	lastCheckString := r.FormValue("lastcheck")
	count2Return := 0
	if len(playerID) > 0 {
		lastCheck, err := strconv.ParseInt(lastCheckString, 10, 64)
		if err != nil {
			lastCheck = 0
		}

		lastCheckTime := time.Unix(lastCheck, 0)
		timeOf48HoursAgo := time.Now().AddDate(0, 0, -2)
		if lastCheckTime.Before(timeOf48HoursAgo) {
			lastCheckTime = timeOf48HoursAgo
		}
		if value, err := CountFightsByUUIDSince(playerID, lastCheckTime); err == nil {
			count2Return = value
		}
	}

	ret := base.SM{
		"result": count2Return,
	}
	ret.Write(w)
}

func GoverHandler(w http.ResponseWriter, r *http.Request) {
	log.Println("gover")

	pid := r.FormValue("pid")
	newName := r.FormValue("newname")
	countOfSoldierString := r.FormValue("newcountofsoldier")
	latitudeString := r.FormValue("lat")
	longitudeString := r.FormValue("lon")

	if len(pid) == 0 {
		return
	}
	countOfSoldierInt, err := strconv.Atoi(countOfSoldierString)
	if err != nil {
		log.Println(err)
		return
	}
	latitudeInt, err := strconv.Atoi(latitudeString)
	if err != nil {
		log.Println(err)
		return
	}
	longitudeInt, err := strconv.Atoi(longitudeString)
	if err != nil {
		log.Println(err)
		return
	}

	territoryFound, err := FindTerritoryByCoordinate(latitudeInt, longitudeInt)
	if err != nil {
		log.Println(err)
		return
	}
	if territoryFound.OwnerUUID != pid {
		// 这地盘都不是你的,来管个毛啊
		return
	}

	accountFound, err := FindAccountByUUID(pid)
	if err != nil {
		log.Println(err)
		return
	}

	countOfSoldierFromAccount := countOfSoldierInt - territoryFound.ArmyQuantity
	if accountFound.ArmyQuantity < countOfSoldierFromAccount {
		// 如果帐号对应的士兵数比向驻城增兵数量还要少,怎么增兵啊
		return
	}
	if len(newName) > 0 {
		territoryFound.Name = newName
	}
	territoryFound.ArmyQuantity = countOfSoldierInt
	accountFound.ArmyQuantity = accountFound.ArmyQuantity - countOfSoldierFromAccount

	if err = UpdateTerritoryAfterGover(territoryFound); err != nil {
		log.Println(err)
	}
	if err = UpdateAccountAfterGover(accountFound); err == nil {
		ret := base.SM{
			"soldierleft": accountFound.ArmyQuantity,
		}
		ret.Write(w)
	}
}

func SearchTreasureHandler(w http.ResponseWriter, r *http.Request) {
	log.Println("searchtreasure")

	pid := r.FormValue("pid")
	latitudeString := r.FormValue("lat")
	longitudeString := r.FormValue("lon")

	if len(pid) == 0 {
		return
	}
	latitudeInt, err := strconv.Atoi(latitudeString)
	if err != nil {
		log.Println(err)
		return
	}
	longitudeInt, err := strconv.Atoi(longitudeString)
	if err != nil {
		log.Println(err)
		return
	}

	if randomGenerator.Intn(1000) < 1 {
		if err := UpdateAllTerritoryAsTreasureSearchable(); err == nil {
			log.Println("刷新隐藏宝藏")
		}
	}

	territoryFound, err := FindTerritoryByCoordinate(latitudeInt, longitudeInt)
	if err != nil {
		log.Println(err)
		return
	}

	UpdateTerritoryAfterSearch(territoryFound)

	if territoryFound.TreasureSearchable {
		if randomGenerator.Intn(2) < 1 {
			if err = UpdateTerritoryAsTreasureUnsearchable(territoryFound); err == nil {
				goldFound := randomGenerator.Intn(900) + 100

				if err = UpdateAccountOfIncreaseGoldByUUID(pid, goldFound); err == nil {
					ret := base.SM{
						"goldfound": goldFound,
					}
					ret.Write(w)
				}
			}
		}
	}
}

func TerritoryHandler(w http.ResponseWriter, r *http.Request) {
	log.Println("territory")

	latitudeString := r.FormValue("lat")
	longitudeString := r.FormValue("lon")

	latitudeInt, err := strconv.Atoi(latitudeString)
	if err != nil {
		return
	}
	longitudeInt, err := strconv.Atoi(longitudeString)
	if err != nil {
		return
	}

	if territory, err := FindTerritoryByCoordinate(latitudeInt, longitudeInt); err == nil {
		ret := territory.writeAsJsonable()
		ret.Write(w)
	}
}

func ShowoffHandler(w http.ResponseWriter, r *http.Request) {
	playerID := r.FormValue("pid")
	infor := CalculateAchievementByPlayerID(playerID)

	infor.Write(w)
}

func PartOfCountryHandler(w http.ResponseWriter, r *http.Request) {
	if countOfLocations, err := strconv.Atoi(r.FormValue("countoflocations")); err == nil {
		size, partOfMatchedCountry, nameOfMatchedCountry := calculateSizeOfCountry(countOfLocations)

		sm := base.SM{}
		sm["Size"] = size
		sm["NameOfMatchedCountry"] = nameOfMatchedCountry
		sm["PartOfMatchedCountry"] = partOfMatchedCountry

		sm.ZipWrite(w)
	}
}

func InfoHandler(w http.ResponseWriter, r *http.Request) {
	log.Println("info")

	ret := base.SM{}

	lengthOfB := 0
	lengthOfK := 0
	lengthOfM := 0
	lengthOfG := 0

	lengthOfB = base.ReadLengthOfOutputBytes()
	if lengthOfB >= 1024 {
		lengthOfK = lengthOfB / 1024
		lengthOfB = lengthOfB % 1024
	}
	if lengthOfK >= 1024 {
		lengthOfM = lengthOfK / 1024
		lengthOfK = lengthOfK % 1024
	}
	if lengthOfM >= 1024 {
		lengthOfG = lengthOfM / 1024
		lengthOfM = lengthOfM % 1024
	}

	outputString := strconv.Itoa(lengthOfG) + "G" + strconv.Itoa(lengthOfM) + "M" + strconv.Itoa(lengthOfK) + "K" + strconv.Itoa(lengthOfB) + "B"

	ret["流量"] = base.SM{
		"starttime": base.ReadServerStartTime().String(),
		"output":    outputString,
	}

	ret["帐户"] = SummaryAccount()
	ret["地块"] = SummaryTerritory()
	ret["战斗"] = SummaryFight()

	ret.ZipWrite(w)
}
