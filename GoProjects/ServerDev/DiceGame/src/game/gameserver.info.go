package game

import (
	"ws/base"
	"log"
	"net/http"
)

func (self *DGGameServer) PrintMissions(playerUUID string, w http.ResponseWriter) {
	missions := make([]string, 0)
	log.Println("check mission:", playerUUID)
	if len(playerUUID) > 0 {
		if !self.alreadyGotAttendanceAward(playerUUID) {
			missions = append(missions, MISSION_DAILY_GAME_EVERYDAY)
		}
		if !self.alreadyGotPrivateRoomAward(playerUUID) {
			missions = append(missions, MISSION_DAILY_GAME_IN_PRIVATE_ROOM)
		}
	}

	ret := base.SM{
		"mission": missions,
	}
	ret.ZipWrite(w)
}

/*
func (self *DGGameServer) PrintSummary(w http.ResponseWriter) {
	ret := make(map[string]interface{})

	rows, err := self.db.Query("select R.*, ifnull(P.CountOfLastPlay, 0) CountOfLastPlay, ifnull(P.CountOfCreated, 0) CountOfCreated from (select S2.*, ifnull(S1.RoomCreated, 0) RoomCreated, ifnull(S1.PrivateRoomCreated, 0) PrivateRoomCreated,ifnull(S1.MaxPublicRooms, 0) MaxPublicRooms, ifnull(S1.MaxPrivateRooms, 0) MaxPrivateRooms, ifnull(S1.MaxRooms, 0) MaxRooms, IFNULL(S1.MaxHumans,0) MaxHumans from (select date(SUMMARY.`when`) YMD, count(*) RoomCreated, sum(if(is_created_a_private_room=1,1,0)) PrivateRoomCreated,max(count_of_public_rooms) MaxPublicRooms, max(count_of_private_rooms) MaxPrivateRooms, max(count_of_public_rooms + count_of_private_rooms) MaxRooms, max(count_of_real_players) MaxHumans from SUMMARY group by YMD order by YMD desc limit 10) S1 right join (select date(ROUNDSUMMARY.`when`) YMD, count(*) RoundCreated from ROUNDSUMMARY group by YMD order by YMD desc limit 10) S2 on S1.YMD = S2.YMD) R left join (select P2.*, P1.CountOfCreated from (select date(created) YMD, COUNT(*) CountOfCreated from PLAYER group by YMD order by YMD desc limit 10) P1 right join (select date(lastplay) YMD, COUNT(*) CountOfLastPlay from PLAYER group by YMD order by YMD desc limit 10) P2 on P1.YMD=P2.YMD) P on R.YMD=P.YMD")
	defer rows.Close()

	if err == nil {
		array := make([]map[string]interface{}, 0)
		for rows.Next() {
			var date string
			var roundCreated int
			var roomCreated int
			var privateRoomCreated int
			var maxPublicRooms int
			var maxPrivateRooms int
			var maxRooms int
			var maxHumans int
			var countOfLastPlay int
			var countOfCreated int

			rows.Scan(&date, &roundCreated, &roomCreated, &privateRoomCreated, &maxPublicRooms, &maxPrivateRooms, &maxRooms, &maxHumans, &countOfLastPlay, &countOfCreated)

			array = append(array, map[string]interface{}{
				"日期":         date,
				"总回合数":       roundCreated,
				"总共创建的房间数":   roomCreated,
				"总共创建的私密房间数": privateRoomCreated,
				"同时最多公共房间数":  maxPublicRooms,
				"同时最多私密房间数":  maxPrivateRooms,
				"同时最多房间数":    maxRooms,
				"同时最多真人玩家数":  maxHumans,
				"当天玩家":       countOfLastPlay,
				"当天新进玩家":     countOfCreated,
			})
		}

		ret["information"] = array
	}

	bytes, err := json.Marshal(ret)
	if err == nil {
		w.Write(bytes)
	}
}
*/

/*
func (self *DGGameServer) PrintRankByUUID(w http.ResponseWriter, uuid string) {
	if uuid == "" {
		return
	}

	var (
		myWins    int
		myAttacks int
		myDefends int
	)

	personalScoreRows, err := self.db.Query("select win, attack, defend from PLAYER where uuid='" + uuid + "'")
	defer personalScoreRows.Close()
	if err != nil {
		return
	}
	if personalScoreRows.Next() {
		personalScoreRows.Scan(&myWins, &myAttacks, &myDefends)
	}

	personalHumanRankRows, _ := self.db.Query("select WR.CountOfWins, WR.CountOfAttacks, S.CountOfDefends from (select W.*, R.CountOfAttacks from (select 1 Mark, count(*) CountOfWins from PLAYER where win > " + strconv.Itoa(myWins) + ") W left join (select 1 Mark, count(*) CountOfAttacks from PLAYER where attack > " + strconv.Itoa(myAttacks) + ") R on W.Mark = R.Mark) WR left join (select 1 Mark, count(*) CountOfDefends from PLAYER where defend > " + strconv.Itoa(myDefends) + ") S on WR.Mark = S.Mark;")
	personalRobotRankRows, _ := self.db.Query("select WR.CountOfWins, WR.CountOfAttacks, S.CountOfDefends from (select W.*, R.CountOfAttacks from (select 1 Mark, count(*) CountOfWins from ROBOT where win > " + strconv.Itoa(myWins) + ") W left join (select 1 Mark, count(*) CountOfAttacks from ROBOT where attack > " + strconv.Itoa(myAttacks) + ") R on W.Mark = R.Mark) WR left join (select 1 Mark, count(*) CountOfDefends from ROBOT where defend > " + strconv.Itoa(myDefends) + ") S on WR.Mark = S.Mark;")
	defer personalHumanRankRows.Close()
	defer personalRobotRankRows.Close()

	var (
		winRankOfHuman    int
		winRankOfRobot    int
		attackRankOfHuman int
		attackRankOfRobot int
		defendRankOfHuman int
		defendRankOfRobot int
	)
	if personalHumanRankRows.Next() && personalRobotRankRows.Next() {
		personalHumanRankRows.Scan(&winRankOfHuman, &attackRankOfHuman, &defendRankOfHuman)
		personalRobotRankRows.Scan(&winRankOfRobot, &attackRankOfRobot, &defendRankOfRobot)
	}

	ret := make(map[string]interface{})

	ret["myWins"] = myWins
	ret["myAttacks"] = myAttacks
	ret["myDefends"] = myDefends
	ret["myWinRank"] = winRankOfHuman + winRankOfRobot + 1
	ret["myAttackRank"] = attackRankOfHuman + attackRankOfRobot + 1
	ret["myDefendRank"] = defendRankOfHuman + defendRankOfRobot + 1

	ret["top10Winners"] = self.top10Query("win")
	ret["top10Attackers"] = self.top10Query("attack")
	ret["top10Defenders"] = self.top10Query("defend")

	bytes, err := json.Marshal(ret)
	if err == nil {
		w.Write(bytes)
	}
}
*/

/*
func (self *DGGameServer) top10Query(orderby string) []map[string]interface{} {
	top10 := make([]map[string]interface{}, 0)

	rows, _ := self.db.Query("select * from ((select uuid, name, win, attack, defend from PLAYER order by " + orderby + " desc limit 10) union (select id, name, win, attack, defend from ROBOT order by " + orderby + " desc limit 10)) PR order by " + orderby + " desc limit 10")
	defer rows.Close()
	for rows.Next() {
		var (
			uuid        string
			name        string
			timesWin    int
			timesAttack int
			timesDefend int
		)

		rows.Scan(&uuid, &name, &timesWin, &timesAttack, &timesDefend)
		top10 = append(top10, map[string]interface{}{
			"uuid":    uuid,
			"name":    name,
			"wins":    timesWin,
			"attacks": timesAttack,
			"defends": timesDefend,
		})
	}

	return top10
}
*/
