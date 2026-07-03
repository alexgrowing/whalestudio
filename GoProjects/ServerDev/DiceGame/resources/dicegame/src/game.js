(function () {
    window.onload = function () {
        game.init()
    };
    
    var game = window.game = {
        width:0,
        height:0,
        scale:0,

        uuid:null,
        sessionID:null,

        asset:null,
        stage:null,
        ticker:null,

        loginScene:null,
        frontPageScene:null,
        gameScene:null,

        init : function () {
            this.asset = new game.Asset();
            this.asset.on("complete", function(e) {
                this.asset.off("complete");
                this.initStage();
            }.bind(this));

            this.asset.load()
        },

        initStage : function() {
            this.width = Math.min(innerWidth, 400) * 2;
            this.height = Math.min(innerHeight, 750) * 2;

            this.scale = 0.5;

            this.asset.FIXED_WIDTH_OF_MIDDLE_BUTTON = this.width/15*4;
            this.asset.FIXED_HEIGHT_OF_MIDDLE_BUTTON = this.asset.FIXED_WIDTH_OF_MIDDLE_BUTTON/3;

            var containerDom = document.getElementById("container");
            containerDom.innerHTML = "";
            containerDom.style.width = this.width * this.scale + "px";
            containerDom.style.height = this.height * this.scale + "px";

            this.stage = new Hilo.Stage({
                width:this.width,
                height:this.height,
                scaleX:this.scale,
                scaleY:this.scale
            });

            containerDom.appendChild(this.stage.canvas);

            this.ticker = new Hilo.Ticker(60);
            this.ticker.addTick(this.stage);
            this.ticker.addTick(Hilo.Tween);
            this.ticker.start();

            this.stage.enableDOMEvent(Hilo.event.POINTER_END, true);

            this.initBackground();
            this.initScenes();

            this.login(function(success, uuid) {
                if (success) {
                    this.uuid = uuid;

                    this.setVisibleScene(this.frontPageScene);

                    if (window.__go2RoomID__.length > 0) {
                        this.setVisibleScene(this.gameScene);
                        this.gameScene.switchView2MatchingPlayers(true);

                        this.createSessionID(function() {
                            this.longpolling();

                            var roomID = window.__go2RoomID__;
                            delete window.__go2RoomID__;
                            this.notifyServerOfGo2ASpecifiedRoom(roomID);
                        }.bind(this));
                    }
                }
            }.bind(this));
        },
        
        initBackground:function () {
            var bgWidth = this.width * this.scale;
            var bgHeight = this.height * this.scale;

            document.getElementById("container").insertBefore(Hilo.createElement("div", {
                id:"bg",
                style:{
                    position:"absolute",
                    background:"url(images/background_1920_1080.jpg) no-repeat",
                    // backgroundSize:bgWidth + "px, " + bgHeight + "px",
                    "background-size":"cover",
                    width:bgWidth + "px",
                    height:bgHeight + "px"
                }
            }), this.stage.canvas)

            /*
            var bgImg = this.asset.bg
            this.bg = new Hilo.Bitmap({
                id : "bg",
                image : bgImg,
                scaleX : this.width / bgImg.width,
                scaleY : this.height / bgImg.height
            }).addTo(this.stage)
            */
        },

        initScenes:function () {
            this.initLoginScene();
            this.initFrontPageScene();
            this.initGameScene();
        },

        setVisibleScene:function (scene) {
            this.loginScene.visible = false;
            this.frontPageScene.visible = false;
            this.gameScene.visible = false;

            scene.visible = true;
        },

        initLoginScene:function() {
            this.loginScene = new game.LoginScene({
                id:"loginscene",
                width:this.width,
                height:this.height,
                wsAsset:this.asset
            }).addTo(this.stage);
        },

        initFrontPageScene:function() {
            this.frontPageScene = new game.FrontPageScene({
                id:"frontpagescene",
                width:this.width,
                height:this.height,
                visible:false,
                wsAsset:this.asset
            }).addTo(this.stage);

            this.frontPageScene.quickstartButton.on(Hilo.event.POINTER_END, function(e) {
                this.setVisibleScene(this.gameScene);
                this.gameScene.switchView2MatchingPlayers();

                this.createSessionID(function() {
                    this.longpolling();

                    this.notifyServerOfQuickStart4();
                }.bind(this));
            }.bind(this));
            this.frontPageScene.arenaButton.on(Hilo.event.POINTER_END, function(e) {
                this.setVisibleScene(this.gameScene);
                this.gameScene.switchView2MatchingPlayers();

                this.createSessionID(function() {
                    this.longpolling();

                    this.notifyServerOfRing();
                }.bind(this));
            }.bind(this));

            this.frontPageScene.createprivateButton.on(Hilo.event.POINTER_END, function(e) {
                this.setVisibleScene(this.gameScene);
                this.gameScene.switchView2MatchingPlayers(true);

                this.createSessionID(function() {
                    this.longpolling();

                    this.notifyServerOfCreateANewRoom();
                }.bind(this));
            }.bind(this));
            this.frontPageScene.intoprivateButton.on(Hilo.event.POINTER_END, function(e) {
                console.log("go into private room")
                // this.createPromptView({
                //     wsMessage:"房间号"
                // }).visible = true;
            }.bind(this.frontPageScene));

            this.frontPageScene.rankButton.on(Hilo.event.POINTER_END, function(e) {
                console.log("go rank")
            });
            this.frontPageScene.informationButton.on(Hilo.event.POINTER_END, function(e) {
                console.log("go information")
            });
        },

        initGameScene:function () {
            this.gameScene = new game.GameScene({
                id:"gamescene",
                width:this.width,
                height:this.height,
                visible:false,
                wsAsset:this.asset
            }).addTo(this.stage);

            this.gameScene.delegateOfGameScene = this;
        },
        
        login:function (callback) {
            var passcodeSavedInCookie = $.cookie("passcode");
            if (passcodeSavedInCookie != null) {
                this.loginByPasscode(passcodeSavedInCookie, function (success, uuid) {
                    if (success) {
                        this.resetPasscodeSavedByCookie(passcodeSavedInCookie);

                        callback(true, uuid)
                    } else {
                        this.loginByCreateAccount(callback);
                    }
                }.bind(this));
            } else {
                this.loginByCreateAccount(callback);
            }
        },

        loginByPasscode:function(passcode, callback) {
            $.ajax({
                url:"../quick?passcode=" + passcode,
                context:this,
                complete:function (res, status) {
                    var json = res.responseJSON;
                    if (json["uuid"] != null) {
                        callback(true, json["uuid"]);
                    } else {
                        callback(false, json["error"]);
                    }
                }.bind(this)
            })
        },

        loginByCreateAccount:function (callback) {
            $.ajax({
                url:"../createquickaccount",
                context:this,
                complete:function(res, status) {
                    var json = res.responseJSON;

                    if (json["uuid"] != null) {
                        this.resetPasscodeSavedByCookie(json["passcode"]);
                        callback(true, json["uuid"]);
                    } else {
                        callback(false, null);
                    }
                }.bind(this)
            })
        },

        resetPasscodeSavedByCookie:function(passcode) {
            $.cookie("passcode", passcode, {
                expires:7
            })
        },

        createSessionID:function(callback) {
            $.ajax({
                url:"../session/create",
                context:this,
                complete:function(res, status) {
                    this.sessionID = res.responseText;
                    callback();
                }.bind(this)
            })
        },

        stopPolling:function () {
            this.sessionID = null;
        },

        longpolling:function() {
            this.polling(function (json) {
                if (json["LOOP"] != null) {
                    if (json["LOOP"]) {
                        this.longpolling();
                    } else {
                        console.log("session id not exist");
                    }
                } else {
                    this.dealWithMessageFromPoll(json);

                    this.longpolling();
                }
            }.bind(this))
        },

        polling:function(callback) {
            if (this.sessionID == null) {
                return;
            }

            $.ajax({
                url:"/session/poll?sid=" + this.sessionID,
                context:this,
                complete:function (res, status) {
                    callback(res.responseJSON);
                }.bind(this)
            });
        },

        sendMessage2Server:function(json) {
            $.ajax({
                url:"../g",
                context:this,
                type:"POST",
                data:{sid:this.sessionID, json:JSON.stringify(json)},
                complete:function(res, status) {
                    console.log(res.responseJSON);
                }.bind(this)
            })
        },

        dealWithMessageFromPoll:function(json) {
            console.log("messages from poll:" + JSON.stringify(json));

            switch (json["operation"]) {
                case "roomid":
                    this.gameScene.beNotifiedOfMyRoomID(json["roomid"], json["typeofroom"]);
                    break;
                case "startround":
                    this.gameScene.switchView2RoundStart();
                    this.gameScene.beNotified2StartRound(json["roundindex"], json["cardinformation"], json["players"]);
                    break;
                case "cardused":
                    this.gameScene.beNotifiedOfCardUsed(json["typeofcard"], json["playerid"], json["someplayeruuids"]);
                    break;
                case "cardnotavailable":
                    this.gameScene.beNotifiedOfMyCard2UseNotAvailable(json["invalidmessage"]);
                    break;
                case "onclienthasshakeddice":
                    this.gameScene.beNotifiedOfOneClientHasShakedDice(json["playerid"]);
                    break;
                case "oneclientcanguessdicenow":
                    this.gameScene.beNotifiedOfOneClient2Guess(json["playerid"]);
                    break;
                case "itisnotyourturn2guess":
                    this.gameScene.beNotifiedOfNotMyTurn2Guess();
                    break;
                case "itisnottime2pointoutliar":
                    this.gameScene.beNotifiedOfNotTime2PointOutLiar();
                    break;
                case "yourlastguessisnotvalid":
                    this.gameScene.beNotifiedOfMyLastGuessIsInvalid(json["invalidmessage"]);
                    break;
                case "someonetakeaguess":
                    this.gameScene.beNotifiedOfGuessByPlayer(json["guess"], json["playerid"], json["nextplayerid"]);
                    break;
                case "someonenotbelievetheguessandopencupnow":
                    this.gameScene.beNotified2OpenCup(json["playerid"]);
                    break;
                case "roundoverandresultisandgo4nextround":
                    this.gameScene.beNotifiedOfRoundResult(json["roundresult"]);
                    break;
                case "oneclientisready4newround":
                    this.gameScene.beNotifiedOfOneClientIsReady4NewRound(json["playerid"]);
                    break;
                case "endgameofservercrashed":
                    this.gameScene.beNotified2EndGameOfServerCrashed();
                    break;
                case "endgameofsomeonelostconnection2server":
                    this.gameScene.beNotified2EndGameOfSomeoneLostConnectionFromServer(json["playerid"]);
                    break;
                case "endgameofsomeoneask4exit":
                    this.gameScene.beNotified2EndGameOfSomeoneAsk2ExitGame(json["playerid"]);
                    break;
                default:
                    break;
            }
        },

        // Delegate Of Game Scene
        myUUID:function () {
            return this.uuid;
        },

        back2MainMenu:function () {
            this.setVisibleScene(this.frontPageScene);

            this.stopPolling();
        },

        notifyServerOfQuickStart4:function () {
            this.sendMessage2Server(messages.quickstart4(this.uuid));
        },

        notifyServerOfRing:function () {
            this.sendMessage2Server(messages.ring(this.uuid));
        },

        notifyServerOfCreateANewRoom:function () {
            this.sendMessage2Server(messages.createanewroom(this.uuid));
        },

        notifyServerOfGo2ASpecifiedRoom:function (roomID) {
            this.sendMessage2Server(messages.go2aspecifiedroom(this.uuid, roomID));
        },

        notifyServerIHaveShakedDice:function () {
            this.sendMessage2Server(messages.ihaveshakeddice(this.uuid));
        },

        notifyServerMyGuess:function(guess) {
            this.sendMessage2Server(messages.myGuessIs(this.uuid, guess));
        },

        notifyServerIDoNotBelieve:function () {
            this.sendMessage2Server(messages.iDoNotBelieve(this.uuid));
        },

        notifyServerMyDicesShaked:function (numbers) {
            this.sendMessage2Server(messages.myDicesAre(this.uuid, numbers));
        },

        notifyServerIAmReady4NewRound:function () {
            this.sendMessage2Server(messages.iAmReady4NewRound(this.uuid));
        },

        notifyServerIWant2EndGame:function () {
            this.sendMessage2Server(messages.iWant2EndGame(this.uuid));
        }
    };
})();