(function () {
    var messages = window.messages = {
        quickstart:function (uuid) {
            return {
                operation : "quickstart",
                uuid:uuid
            }
        }, quickstart4:function (uuid) {
            return {
                operation : "quickstart4",
                uuid:uuid
            }
        }, ring:function(uuid) {
            return {
                operation : "ring",
                uuid:uuid
            }
        }, createanewroom:function(uuid) {
            return {
                operation : "createanewroom",
                uuid:uuid
            }
        }, go2aspecifiedroom:function(uuid, roomid) {
            return {
                operation : "go2aspecifiedroom",
                uuid:uuid,
                roomid:roomid
            }
        }, ihaveshakeddice:function (uuid) {
            return {
                operation : "ihaveshakeddice",
                playerid:uuid
            }
        }, myGuessIs:function (uuid, guess) {
            return {
                operation : "myguessis",
                playerid:uuid,
                guess:{"count":guess.count, "factor":guess.factor}
            }
        }, iDoNotBelieve:function (uuid) {
            return {
                operation : "idonotbelieve",
                playerid:uuid
            }
        }, myDicesAre:function (uuid, numbers) {
            return {
                operation : "mydicesare",
                playerid:uuid,
                dices:numbers
            }
        }, iAmReady4NewRound:function (uuid) {
            return {
                operation : "iamready4newround",
                playerid:uuid
            }
        }, iWant2EndGame:function (uuid) {
            return {
                operation : "iwant2endgame",
                playerid:uuid
            }
        }
    }
})();