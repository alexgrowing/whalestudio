package main

import (
	"log"
	"strconv"
	"net/http"
	"io/ioutil"
	"html/template"
	"encoding/json"
	"ws/base"
)

func main() {
	PORT := 80

	log.Println("监听" + strconv.Itoa(PORT) + "端口...")

	http.Handle("/", http.FileServer(http.Dir("static")))
	http.HandleFunc("/land/showoff", landShowoffHandler)

	log.Fatal(http.ListenAndServe(":"+strconv.Itoa(PORT), nil))
}

func landShowoffHandler(w http.ResponseWriter, r *http.Request) {
	playerID := r.FormValue("pid")

	if resp, err := http.Get("http://localhost:9999/showoff?pid=" + playerID); err == nil {
		if body, err := ioutil.ReadAll(resp.Body); err == nil {
			
			ob := &base.SM{}
			if json.Unmarshal(body, ob) == nil {

				t := template.New("")
				t = template.Must(t.ParseFiles("tpl/showoff.html"))

				t.ExecuteTemplate(w, "showoff.html", ob)
			}
		}
	}

}