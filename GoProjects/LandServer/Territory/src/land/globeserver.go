package land

import (
	"net/http"
	"ws/base"
)

func GlobalTerritoryHandler(w http.ResponseWriter, r *http.Request) {
	jsonTerritories := make([]base.SM, 0)

	if territories, err := FindAllTerritories(); err == nil {
		for _, ter := range territories {
			jsonTerritories = append(jsonTerritories, ter.writeCoordinatAsJsonable())
		}
	}

	ret := base.SM{"territories": jsonTerritories}
	ret.ZipWrite(w)
}
