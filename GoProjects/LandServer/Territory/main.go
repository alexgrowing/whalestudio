package main

import (
	"log"
	"net/http"
	"strconv"

	"land"
)

func main() {
	PORT := 9999
	log.Println("监听" + strconv.Itoa(PORT) + "端口...")

	http.Handle("/html/", http.FileServer(http.Dir("resources")))
	http.Handle("/css/", http.FileServer(http.Dir("resources")))
	http.Handle("/js/", http.FileServer(http.Dir("resources")))
	http.Handle("/img/", http.FileServer(http.Dir("resources")))

	http.HandleFunc("/login13", land.LoginHandler)
	http.HandleFunc("/foot", land.FootprintHandler)
	http.HandleFunc("/rename", land.RenameHandler)
	http.HandleFunc("/purchase", land.PurchaseHandler)
	http.HandleFunc("/step", land.StepHandler)
	http.HandleFunc("/ter", land.TerritoryHandler)
	http.HandleFunc("/rec", land.RecruitSoldierHandler)
	http.HandleFunc("/quickfinishtraining", land.QuickFinishTrainingHandler)
	http.HandleFunc("/brieffights", land.BriefFightsHandler)
	http.HandleFunc("/countofnewfights", land.FetchCountOfNewFightsHandler)
	http.HandleFunc("/gover", land.GoverHandler)
	http.HandleFunc("/searchtreasure", land.SearchTreasureHandler)
	http.HandleFunc("/atta", land.AttackHandler)

	http.HandleFunc("/showoff", land.ShowoffHandler)
	http.HandleFunc("/partofcountry", land.PartOfCountryHandler)

	http.HandleFunc("/info", land.InfoHandler)

	http.HandleFunc("/login", land.DeprecatedHandler)
	http.HandleFunc("/attack", land.DeprecatedHandler)

	http.HandleFunc("/l", land.DeprecatedHandler)
	http.HandleFunc("/recruit", land.DeprecatedHandler)

	http.HandleFunc("/global/terr", land.GlobalTerritoryHandler)

	log.Fatal(http.ListenAndServe(":"+strconv.Itoa(PORT), nil))
}
