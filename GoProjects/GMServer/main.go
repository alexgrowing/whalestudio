package main

import (
	"encoding/json"
	"fmt"
	"geolocate"
	"log"
	"net/http"
	"strconv"
)

var client = geolocate.NewGoogleGeo("AIzaSyDY7yfkjDzsZZkkCjwrkR9XNcE8egqLmzM")
var feedback_error = "ERROR"

/*
func main() {
	res, _ := client.Geocode("富力城")
	fmt.Println(res)

	p := geolocate.Point{Lat: 40.7127837, Lng: -74.0059413}
	res2, _ := client.ReverseGeocode(&p)
	fmt.Println(res2)
}
*/

func main() {
	PORT := 12345
	log.Println("监听" + strconv.Itoa(PORT) + "端口...")

	http.HandleFunc("/address", addressHandle)
	http.HandleFunc("/point", pointHandle)

	log.Fatal(http.ListenAndServe(":"+strconv.Itoa(PORT), nil))
}

func addressHandle(w http.ResponseWriter, r *http.Request) {
	w.Header().Set("content-type", "application/json")

	addressName := r.FormValue("name")
	if res, err := client.Geocode(addressName); err == nil {
		ob := make(map[string]interface{})
		ob["address"] = res.Address
		ob["lat"] = res.Lat
		ob["lng"] = res.Lng

		if bytes, err := json.Marshal(ob); err == nil {
			w.Write(bytes)

			return
		}
	} else {
		log.Println(err.Error())
	}

	w.Write([]byte(feedback_error))
}

func pointHandle(w http.ResponseWriter, r *http.Request) {
	w.Header().Set("content-type", "application/json")

	lat, _ := strconv.ParseFloat(r.FormValue("lat"), 64)
	lng, _ := strconv.ParseFloat(r.FormValue("lng"), 64)

	fmt.Println("lat:", lat, " and lng:", lng)

	p := geolocate.Point{Lat: lat, Lng: lng}
	if res, err := client.ReverseGeocode(&p); err == nil {
		w.Write([]byte(res))
	} else {
		w.Write([]byte(feedback_error))
	}
}
