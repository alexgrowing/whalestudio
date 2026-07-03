package base

const folderNameSavingPlayerFigures = "f"
const folderNameSavingRobotFigures = "fr"

const Card_NAME_RESHAKE = "cardnamereshake"
const CARD_NAME_NEXT = "cardnamenext"

// GetFigureURLOfPlayer GetFigureURLOfPlayer
func GetFigureURLOfPlayer(uuid string) string {
	return "http://www.whalestudio.cn:4004/" + folderNameSavingPlayerFigures + "/" + uuid + ".jpg"
}

// GetFigureURLOfRobot GetFigureURLOfRobot
func GetFigureURLOfRobot(numberID string) string {
	return "http://www.whalestudio.cn:4004/" + folderNameSavingRobotFigures + "/" + numberID + ".jpg"
}
