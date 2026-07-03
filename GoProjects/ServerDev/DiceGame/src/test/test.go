package test

import (
	"fmt"
	"net/http"
)

type BigS struct {
	X int
	Y int
	z int
}

func (bs *BigS) ServeHTTP(w http.ResponseWriter, r *http.Request) {
	fmt.Fprint(w, bs.Y+bs.X)
}
