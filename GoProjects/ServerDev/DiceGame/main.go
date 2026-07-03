package main

import (
	"ws/base"
	"db"
	"encoding/json"
	"fmt"
	"game"
	"log"
	"net/http"
	"strconv"
	"time"
	"longpoll"
	"ws/base/account"
	"html/template"
	dbase "base"
)

func main() {
	PORT := 8888

	log.Println("监听" + strconv.Itoa(PORT) + "端口...")

	account.HandleHttpRequest(&game.AccountListener{})

	http.HandleFunc("/dicegame/start", indexHandler)
	http.Handle("/dicegame/", http.FileServer(http.Dir("resources")))
	http.Handle("/flappy/", http.FileServer(http.Dir("resources")))
	http.Handle("/html/", http.FileServer(http.Dir("resources")))
	http.Handle("/css/", http.FileServer(http.Dir("resources")))
	http.Handle("/js/", http.FileServer(http.Dir("resources")))
	http.Handle("/img/", http.FileServer(http.Dir("resources")))

	http.HandleFunc("/g", gameHandler)

	http.HandleFunc("/u", userHandler)
	http.HandleFunc("/mission", missionHandler)
	http.HandleFunc("/readfeedback", readFeedbackHandler)
	http.HandleFunc("/writefeedback", writeFeedbackHandler)

	http.HandleFunc("/ad", adHandler)

	http.HandleFunc("/session/create", createSessionAction)
	http.HandleFunc("/session/poll", pollAction)
	http.HandleFunc("/session/test", testSendMessageAction)
	http.HandleFunc("/session/alive", showAliveSessionsAction)

	http.HandleFunc("/info", infoHandler)

	http.HandleFunc("/feedback", writeFeedbackHandler)

	http.HandleFunc("/l26", deprecatedHandler)
	http.HandleFunc("/l27", deprecatedHandler)
	http.HandleFunc("/l30", deprecatedHandler)
	http.HandleFunc("/login", deprecatedHandler)

	http.HandleFunc("/", notFoundHandler)

	longpoll.RegisterListener(&SessionListener{})
	log.Fatal(http.ListenAndServe(":"+strconv.Itoa(PORT), nil))
}

func indexHandler(w http.ResponseWriter, r *http.Request) {
	ret := base.SM{}
	ret["token"] = time.Now().Unix()
	//ret["token"] = "1234567890"

	ret["privateroomid"] = r.FormValue("pr")

	t := template.New("")
	t = template.Must(t.ParseFiles("tpl/dicegame.html"))

	t.ExecuteTemplate(w, "dicegame.html", ret)
}

func createSessionAction(w http.ResponseWriter, r *http.Request) {
	fmt.Fprint(w, longpoll.CreateSessionID())
}

func pollAction(w http.ResponseWriter, r *http.Request) {
	sid := r.FormValue("sid")

	longpoll.Poll(sid, w)
}

func testSendMessageAction(w http.ResponseWriter, r *http.Request) {
	sid := r.FormValue("sid")

	longpoll.TestSendMessage(sid)
}

func showAliveSessionsAction(w http.ResponseWriter, r *http.Request) {
	longpoll.SessionsAlive().ZipWrite(w)
}

func deprecatedHandler(w http.ResponseWriter, r *http.Request) {
	log.Println("deprecated")
	ret := base.SM{"deprecated": true}
	ret.ZipWrite(w)
}

/*
func loginHandler(w http.ResponseWriter, r *http.Request) {
	log.Println("login")

	playerID := r.FormValue("pid")
	playerName := r.FormValue("pname")

	ret := base.SM{}
	var accountReturn *db.Player

	if accountFound, err := db.FindPlayerByUUID(playerID); err == nil {
		// 数据库里面有对应的account
		accountReturn = accountFound
	} else {
		if newAccount, err := db.CreateANewPlayerByUUIDAndName(playerID, playerName); err == nil {
			accountReturn = newAccount
		} else {
			ret["error"] = err.Error()
		}
	}

	if accountReturn != nil {
		ret["validuuid"] = accountReturn.UUID
		ret["validname"] = accountReturn.Name

		db.UpdatePlayerLoginInformation(accountReturn)
	}

	ret.Write(w)
}
*/

var gameServer = game.NewDGGameServer()

func gameHandler(w http.ResponseWriter, r *http.Request) {
	w.Header().Set("content-type", "application/json")

	jsonString := r.FormValue("json")

	var jsonOb map[string]interface{}
	if err := json.Unmarshal([]byte(jsonString), &jsonOb); err == nil {
		sid := r.FormValue("sid")

		gameServer.Dispatch(&longpoll.SessionMessageSender2Client{sid}, jsonOb)
		FEEDBACK_OK.ZipWrite(w)
	} else {
		FEEDBACK_NOT_OK.ZipWrite(w)
	}
}

func userHandler(w http.ResponseWriter, r *http.Request) {
	op := r.FormValue("op")
	uuid := r.FormValue("uuid")


	if len(op) == 0 || len(uuid) == 0 {
		return
	}

	w.Header().Set("content-type", "application/json")

	switch op {
	case "view":
		if player, err := db.FindPlayerByUUID(uuid); err == nil {
			sm := base.SM{}
			sm["name"] = player.Name
			sm["figure"] = dbase.GetFigureURLOfPlayer(player.UUID)
			sm["countofgold"] = player.Gold
			sm["countofcrown"] = player.Crown
			sm["countofcards"] = 0

			if cards, err := db.FindCardsByUUID(uuid); err == nil {
				sm["countofcards"] = len(cards)
			}

			sm.ZipWrite(w)
		}
	case "mod":
		if newName := r.FormValue("newname"); len(newName) > 0 {
			db.RenameByUUID(newName, uuid)
		}
	}
}

func missionHandler(w http.ResponseWriter, r *http.Request) {
	gameServer.PrintMissions(r.FormValue("uuid"), w)
}

func infoHandler(w http.ResponseWriter, r *http.Request) {
	ret := base.SM{}

	ret["流量"] = base.SM{
		"starttime": base.ReadServerStartTime().String(),
		"output":    base.LengthOfBytesAsString(base.ReadLengthOfOutputBytes()),
	}
	query_start_time := time.Now()
	// 回合
	ret["回合"] = base.SM{
		"今天":db.RoundsInToday(),
		"N48小时":db.RoundsIn48Hours(),
		"N48小时私密进入":db.PrivateRoomIn48Hours(),
		"calculate_time":time.Now().Sub(query_start_time).String(),
	}
	query_start_time = time.Now()

	if countOfAllRounds, countOfAllHumanRounds, err := db.CountOfTypeOfPlayers(); err == nil {
		ret["历史累计"] = base.SM{
			"总回合数":     countOfAllRounds,
			"真人玩家总回合数": countOfAllHumanRounds,
			"calculate_time":time.Now().Sub(query_start_time).String(),
		}
		query_start_time = time.Now()
	}

	smOfRecent10Rounds := make([]base.SM, 0)
	for _, round := range db.Recent10Rounds() {
		smOfRecent10Rounds = append(smOfRecent10Rounds, base.SM{
			"时间":     round.When,
			"类型":     round.TypeOfRoom,
			"真人":     round.CountOfHuman,
			"机器":     round.CountOfRobot,
			"RoomID": round.RoomID,
		})
	}
	ret["最近10回合"] = base.SM{
		"回合":smOfRecent10Rounds,
		"calculate_time":time.Now().Sub(query_start_time).String(),
	}
	query_start_time = time.Now()

	if latestRoomInfo, err := db.LatestRoomInfo(); err == nil {
		ret["最近一次新增Room"] = base.SM{
			"时间":           latestRoomInfo.When,
			"此时public房间数":  latestRoomInfo.CountOfPublicRooms,
			"此时private房间数": latestRoomInfo.CountOfPrivateRooms,
			"此时ring房间数":    latestRoomInfo.CountOfRingRooms,
			"当前真人玩家数":      latestRoomInfo.CountOfRealPlayers,
			"calculate_time":time.Now().Sub(query_start_time).String(),
		}
		query_start_time = time.Now()
	}

	// 玩家
	if countOfCreated, countOfLastPlay, err := db.CountOfPlayersIn48Hours(); err == nil {
		ret["玩家"] = base.SM{
			"N48小时内新增玩家数": countOfCreated,
			"N48小时内玩家数":   countOfLastPlay,
			"calculate_time":time.Now().Sub(query_start_time).String(),
		}
		query_start_time = time.Now()
	}

	// 卡片
	if usage, err := db.SummaryCardUsage(); err == nil {
		usage["calculate_time"] = time.Now().Sub(query_start_time).String()
		ret["卡片"] = usage
	}

	t := template.New("")
	t = template.Must(t.ParseFiles("tpl/info.html"))

	t.ExecuteTemplate(w, "info.html", ret)
}

func adHandler(w http.ResponseWriter, r *http.Request) {
	gameServer.Reward4AdClicked(r.FormValue("uuid"))
}

func readFeedbackHandler(w http.ResponseWriter, r *http.Request) {
	ret := base.SM{}
	array := make([]string, 0)

	if feedbacks, err := db.FindRecent100Feedback(); err == nil {
		for _, fb := range feedbacks {
			array = append(array, fb.Content)
		}
	}
	ret["information"] = array

	ret.ZipWrite(w);
}

func writeFeedbackHandler(w http.ResponseWriter, r *http.Request) {
	content := r.FormValue("content")
	if content == "" {
		return
	}

	name := r.FormValue("name")
	if name == "" {
		name = "anonymous"
	}

	db.InsertFeedback(name, content)
}

/*
func rankHandler(w http.ResponseWriter, r *http.Request) {
	uuid := r.FormValue("uuid")

	gameServer.PrintRankByUUID(w, uuid)
}
*/

func notFoundHandler(w http.ResponseWriter, r *http.Request) {
	//	if r.URL.Path == "/" {
	//		http.Redirect(w, r, "/login/index", http.StatusFound)
	//	}

	//	t, err := template.ParseFiles("template/html/404.html")
	//	if err != nil {
	//		log.Println(err)
	//	}
	//	t.Execute(w, nil)
}

var FEEDBACK_OK = base.SM{"OK":true}
var FEEDBACK_NOT_OK = base.SM{"OK":false}


type SessionListener struct {}
func (self *SessionListener) OnSessionIDDestroyed(sid string) {
	gameServer.LostConnectionOfSessionID(sid)
}