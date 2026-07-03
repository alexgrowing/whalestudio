package main

import (
"fmt"
"net/http"
)

func handler(w http.ResponseWriter, r *http.Request) {
	fmt.Fprintf(w,
		"Hi, This is an example of https service in golang!")
}

func main() {
	http.HandleFunc("/test", handler)
	http.Handle("/", http.FileServer(http.Dir("resources")))

	http.ListenAndServe(":880",nil)
}

func mainhttps() {
	http.HandleFunc("/test", handler)
	http.Handle("/", http.FileServer(http.Dir("resources")))

	error := http.ListenAndServeTLS(":443", "server.crt",
		"server.key", nil)

	fmt.Print(error)
}

