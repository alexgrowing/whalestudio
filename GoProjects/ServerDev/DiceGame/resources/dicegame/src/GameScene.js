(function (ns) {
    var SIZE_OF_DICE_CUP = 300;
    var SIZE_OF_POINTER = 140;

    var SIZE_OF_FIGURE_IMAGE = 50;
    var HEIGHT_OF_NAME_LABEL = 20;
    var WIDTH_OF_NAME_LABEL = 200;
    var SIZE_OF_ACTION_IMAGE = 30;
    var SIZE_OF_CROWN = 30;
    var PADDING_INSIDE_PLAYER_VIEW = 4;

    var PADDING_BETWEEN_WIDGETS_INSIDE_PLAYER_VIEW = 10;

    var PADDING_AROUND_PLAYER_VIEW = 20;

    var SIZE_OF_DICE = 60;
    var PADDING_BETWEEN_DICES = 10;

    var WIDTH_OF_GUESS_VIEW = SIZE_OF_DICE * 3;
    var HEIGHT_OF_GUESS_VIEW = SIZE_OF_DICE;

    var HEIGHT_OF_PLAYER_VIEW = SIZE_OF_DICE + PADDING_INSIDE_PLAYER_VIEW * 2;

    var HEIGHT_OF_MANI_COUNT_OF_FACTOR_VIEW = SIZE_OF_DICE*2 + PADDING_BETWEEN_DICES*3;

    var SIZE_OF_MANI_COUNT_BUTTON = 40;
    var WIDTH_OF_MANI_COUNT_LABEL = 60;
    var HEIGHT_OF_MANI_COUNT_LABEL = 40;

    var HEIGHT_OF_SCREEN_TOUCH_LABEL = 30;

    var FIVE_UNKNOW_DICES = [0,0,0,0,0];

    var GameScene = ns.GameScene = Hilo.Class.create({
        Extends : ns.Scene,
        constructor : function (properties) {
            GameScene.superclass.constructor.call(this, properties)
            this.init(properties)
        },

        delegateOfGameScene : null,

        allPlayers:null,
        mapOfAllPlayerViews : null,

        matchPlayerContainer:null,
        matchPlayerInformationText:null,

        roomContainer:null,

        dicesITossed:null,
        fiveDicesContainerAfterShake:null,
        shakeDiceCup:null,
        roundInfoLabel:null,
        countingLabel:null,
        pointerImageView:null,
        historyGuessView:null,
        tellLiarLabel:null,

        maniCountOfFactorContainer:null,
        count2Guess:2,
        count2GuessLabel:null,
        decreaseCountButton:null,
        increaseCountButton:null,

        oneHasBeenGuessed:false,
        factor1Button:null,
        factor2Button:null,
        factor3Button:null,
        factor4Button:null,
        factor5Button:null,
        factor6Button:null,
        factorManipulationButtons:[],

        myManipulationContainer:null,
        sendMyGuessButton:null,
        pointOutLiarButton:null,
        useCardButton:null,

        startNewRoundButton:null,
        toMainMenuButton:null,

        screenTouchInfoLabel:null,
        screenTouchAcceptable:false,

        typeOfRoom:1,
        amIWinRound:false,

        init : function (properties) {
            var heightOfAd = 100;

            this.matchPlayerContainer = new Hilo.Container({
                x:0,y:heightOfAd,width:this.width,height:this.height-heightOfAd,
                visible:false
            }).addTo(this);
            this.addSubviews2MatchPlayerContainer();

            this.roomContainer = new Hilo.Container({
                x:0,y:heightOfAd, width:this.width,height:this.height - heightOfAd,
                visible:false
            }).addTo(this);

            this.addSubviews2RoomContainer();

            this.on(Hilo.event.POINTER_END, function (e) {
                if (this.screenTouchAcceptable) {
                    this.startShake();
                }
            }.bind(this));
        },

        addSubviews2MatchPlayerContainer:function () {
            var parent = this.matchPlayerContainer;

            var heightOfText = 60;
            var gap2Center = 100;
            this.matchPlayerInformationText = new Hilo.Text({
                text:"正在匹配玩家",
                font:heightOfText + "px 宋体",
                color:"#FFFFFF",
                textAlign:"center",
                maxWidth:parent.width,
                width:parent.width,
                height:heightOfText,
                x:0,
                y:parent.height / 2 - heightOfText - gap2Center
            }).addTo(parent);

            var cancelButton = this.asset.createMiddleButton({
                text:"取消", color:"black",wsTextHeight:this.asset.FIXED_HEIGHT_OF_MIDDLE_BUTTON/3,
                x:(parent.width - this.asset.FIXED_WIDTH_OF_MIDDLE_BUTTON) / 2, y:parent.height / 2 + gap2Center,
                wsButtonClicked:function () {
                    this.delegateOfGameScene.back2MainMenu();
                }.bind(this)
            }).addTo(parent);
        },

        addSubviews2RoomContainer:function () {
            var parent = this.roomContainer;

            this.fiveDicesContainerAfterShake = new Hilo.Container({
                x:parent.width/2,y:parent.height/2,
                pivotX:SIZE_OF_DICE/2,pivotY:SIZE_OF_DICE/2,
                width:SIZE_OF_DICE,
                height:SIZE_OF_DICE
            }).addTo(parent);
            this.shakeDiceCup = this.asset.createDiceCupImg({
                x:parent.width/2,y:parent.height/2,
                pivotX:SIZE_OF_DICE_CUP/2,pivotY:SIZE_OF_DICE_CUP/2,
                width:SIZE_OF_DICE_CUP,
                height:SIZE_OF_DICE_CUP,
                visible:false
            }).addTo(parent);

            var heightOfRoundInfoLabel = 80;
            var widthOfRoundInfoLabel = parent.width;
            this.roundInfoLabel = new Hilo.Text({
                pivotX:widthOfRoundInfoLabel/2,
                pivotY:heightOfRoundInfoLabel/2,
                x:parent.width/2,y:parent.height/2,
                width:widthOfRoundInfoLabel,
                maxWidth:widthOfRoundInfoLabel,
                height:heightOfRoundInfoLabel,
                font:heightOfRoundInfoLabel + "px 宋体",
                text:"Round 1",
                textAlign:"center",
                color:"white",
                visible:false
            }).addTo(parent);

            this.pointerImageView = this.asset.createPointerImg({
                x:parent.width/2,
                y:parent.height/2,
                width:SIZE_OF_POINTER,
                height:SIZE_OF_POINTER,
                pivotX:SIZE_OF_POINTER/2,
                pivotY:SIZE_OF_POINTER/2,
                visible:false
            }).addTo(parent);
            this.countingLabel = new Hilo.Text({
                font:(SIZE_OF_POINTER/2) + "px 宋体",
                color:"white",
                textAlign:"center",
                textVAlign:"middle",
                x:parent.width/2,
                y:parent.height/2,
                width:SIZE_OF_POINTER,
                height:SIZE_OF_POINTER,
                pivotX:SIZE_OF_POINTER/2,
                pivotY:SIZE_OF_POINTER/2,
                visible:false
            }).addTo(parent);

            this.historyGuessView = new GuessView({
                asset:this.asset,
                x:(parent.width)/2,
                y:(parent.height)/2,
                pivotX:WIDTH_OF_GUESS_VIEW/2,
                pivotY:HEIGHT_OF_GUESS_VIEW/2,
                width:WIDTH_OF_GUESS_VIEW,
                height:HEIGHT_OF_GUESS_VIEW,
                visible:false
            }).addTo(parent);

            this.tellLiarLabel = new Hilo.Text({
                x:(parent.width)/2,
                y:(parent.height)/2,
                pivotX:WIDTH_OF_GUESS_VIEW/2,
                pivotY:HEIGHT_OF_GUESS_VIEW/2,
                width:WIDTH_OF_GUESS_VIEW,
                height:HEIGHT_OF_GUESS_VIEW,
                text:"我不信",
                font:(SIZE_OF_DICE/3*2) + "px 宋体",
                textAlign:"center",
                color:"white",
                visible:false
            }).addTo(parent);

            this.myManipulationContainer = new Hilo.Container({
                x:PADDING_AROUND_PLAYER_VIEW,
                y:parent.height - HEIGHT_OF_PLAYER_VIEW - this.asset.FIXED_HEIGHT_OF_MIDDLE_BUTTON - PADDING_AROUND_PLAYER_VIEW*2,
                width:this.width - PADDING_AROUND_PLAYER_VIEW * 2,
                height:this.asset.FIXED_HEIGHT_OF_MIDDLE_BUTTON,
                visible:false
            }).addTo(parent);

            this.pointOutLiarButton = this.asset.createRedButton({
                x:0,y:0,
                text:"我不信",
                color:"white",
                wsTextHeight:this.asset.FIXED_HEIGHT_OF_MIDDLE_BUTTON/3,
                wsButtonClicked:function (e) {
                    this.sendMyGuessButton.setEnabled(false);
                    this.pointOutLiarButton.setEnabled(false);

                    this.delegateOfGameScene.notifyServerIDoNotBelieve();
                }.bind(this)
            }).addTo(this.myManipulationContainer);

            this.sendMyGuessButton = this.asset.createGreenButton({
                x:(this.myManipulationContainer.width-this.asset.FIXED_WIDTH_OF_MIDDLE_BUTTON)/2,y:0,
                text:"我猜",
                color:"white",
                wsTextHeight:this.asset.FIXED_HEIGHT_OF_MIDDLE_BUTTON/3,
                wsButtonClicked:function (e) {
                    this.sendMyGuessButton.setEnabled(false);
                    this.pointOutLiarButton.setEnabled(false);

                    this.delegateOfGameScene.notifyServerMyGuess(this.getSelectedGuess());
                }.bind(this)
            }).addTo(this.myManipulationContainer);

            this.maniCountOfFactorContainer = new Hilo.Container({
                x:HEIGHT_OF_PLAYER_VIEW + PADDING_AROUND_PLAYER_VIEW * 2,
                y:this.myManipulationContainer.y - PADDING_AROUND_PLAYER_VIEW - HEIGHT_OF_MANI_COUNT_OF_FACTOR_VIEW,
                width:parent.width-(HEIGHT_OF_PLAYER_VIEW + PADDING_AROUND_PLAYER_VIEW * 2)*2,
                height:HEIGHT_OF_MANI_COUNT_OF_FACTOR_VIEW,
                visible:false
            }).addTo(parent);

            var widthOfHalfCountOfFactorContainer = this.maniCountOfFactorContainer.width/2;
            var maniCountContainer = new Hilo.Container({
                x:0,y:0,
                width:widthOfHalfCountOfFactorContainer,
                height:this.maniCountOfFactorContainer.height
            }).addTo(this.maniCountOfFactorContainer);

            var horizontalGapInsideManiCountContainer = (maniCountContainer.width-SIZE_OF_MANI_COUNT_BUTTON*2-WIDTH_OF_MANI_COUNT_LABEL)/4;
            this.count2GuessLabel = new Hilo.Text({
                x:(maniCountContainer.width-WIDTH_OF_MANI_COUNT_LABEL)/2,
                y:(maniCountContainer.height-HEIGHT_OF_MANI_COUNT_LABEL)/2,
                width:WIDTH_OF_MANI_COUNT_LABEL,
                height:HEIGHT_OF_MANI_COUNT_LABEL,
                text:this.count2Guess,
                font:HEIGHT_OF_MANI_COUNT_LABEL + "px 宋体",
                color:"white",
                textAlign:"center"
            }).addTo(maniCountContainer);
            this.decreaseCountButton = this.asset.createMinusImg({
                x:horizontalGapInsideManiCountContainer,
                y:(maniCountContainer.height - SIZE_OF_MANI_COUNT_BUTTON)/2,
                width:SIZE_OF_MANI_COUNT_BUTTON,
                height:SIZE_OF_MANI_COUNT_BUTTON
            }).addTo(maniCountContainer);
            this.decreaseCountButton.on(Hilo.event.POINTER_END, function (e) {
                this.setCount2Guess(this.count2Guess - 1);
            }.bind(this));
            this.increaseCountButton = this.asset.createPlusImg({
                x:maniCountContainer.width-horizontalGapInsideManiCountContainer-SIZE_OF_MANI_COUNT_BUTTON,
                y:(maniCountContainer.height - SIZE_OF_MANI_COUNT_BUTTON)/2,
                width:SIZE_OF_MANI_COUNT_BUTTON,
                height:SIZE_OF_MANI_COUNT_BUTTON
            }).addTo(maniCountContainer);
            this.increaseCountButton.on(Hilo.event.POINTER_END, function (e) {
                this.setCount2Guess(this.count2Guess + 1)
            }.bind(this));

            var maniFactorContainer = new Hilo.Container({
                x:widthOfHalfCountOfFactorContainer,y:0,
                width:widthOfHalfCountOfFactorContainer,
                height:this.maniCountOfFactorContainer.height
            }).addTo(this.maniCountOfFactorContainer);

            var horizontalGapBetweenDices = (maniFactorContainer.width-SIZE_OF_DICE*3)/4;
            var buttonclickedOnSelectableDiceButton = function (number) {
                this.setSelectedManipulationDiceNumber(number);
            }.bind(this);
            this.factor1Button = new SelectableDiceButton({
                asset:this.asset,
                number:1,
                x:horizontalGapBetweenDices,
                y:PADDING_BETWEEN_DICES,
                width:SIZE_OF_DICE,
                height:SIZE_OF_DICE,
                wsButtonClicked:buttonclickedOnSelectableDiceButton
            }).addTo(maniFactorContainer);

            this.factor2Button = new SelectableDiceButton({
                asset:this.asset,
                number:2,
                x:(maniFactorContainer.width-SIZE_OF_DICE)/2,
                y:PADDING_BETWEEN_DICES,
                width:SIZE_OF_DICE,
                height:SIZE_OF_DICE,
                wsButtonClicked:buttonclickedOnSelectableDiceButton
            }).addTo(maniFactorContainer);

            this.factor3Button = new SelectableDiceButton({
                asset:this.asset,
                number:3,
                x:maniFactorContainer.width-horizontalGapBetweenDices-SIZE_OF_DICE,
                y:PADDING_BETWEEN_DICES,
                width:SIZE_OF_DICE,
                height:SIZE_OF_DICE,
                wsButtonClicked:buttonclickedOnSelectableDiceButton
            }).addTo(maniFactorContainer);

            this.factor4Button = new SelectableDiceButton({
                asset:this.asset,
                number:4,
                x:horizontalGapBetweenDices,
                y:maniFactorContainer.height-PADDING_BETWEEN_DICES-SIZE_OF_DICE,
                width:SIZE_OF_DICE,
                height:SIZE_OF_DICE,
                wsButtonClicked:buttonclickedOnSelectableDiceButton
            }).addTo(maniFactorContainer);

            this.factor5Button = new SelectableDiceButton({
                asset:this.asset,
                number:5,
                x:(maniFactorContainer.width-SIZE_OF_DICE)/2,
                y:maniFactorContainer.height-PADDING_BETWEEN_DICES-SIZE_OF_DICE,
                width:SIZE_OF_DICE,
                height:SIZE_OF_DICE,
                wsButtonClicked:buttonclickedOnSelectableDiceButton
            }).addTo(maniFactorContainer);

            this.factor6Button = new SelectableDiceButton({
                asset:this.asset,
                number:6,
                x:maniFactorContainer.width-horizontalGapBetweenDices-SIZE_OF_DICE,
                y:maniFactorContainer.height-PADDING_BETWEEN_DICES-SIZE_OF_DICE,
                width:SIZE_OF_DICE,
                height:SIZE_OF_DICE,
                wsButtonClicked:buttonclickedOnSelectableDiceButton
            }).addTo(maniFactorContainer);

            this.factorManipulationButtons = [
                this.factor1Button,
                this.factor2Button,
                this.factor3Button,
                this.factor4Button,
                this.factor5Button,
                this.factor6Button
            ];
            this.setSelectedManipulationDiceNumber(1);

            var gapBetweenEndRoundButtons = (parent.width - this.asset.FIXED_WIDTH_OF_MIDDLE_BUTTON*2)/3;
            var yPosOfEndRoundButtons = this.myManipulationContainer.y;
            this.startNewRoundButton = this.asset.createMiddleButton({
                text:"新回合",color:"black",wsTextHeight:this.asset.FIXED_HEIGHT_OF_MIDDLE_BUTTON/3,
                x:gapBetweenEndRoundButtons,
                y:yPosOfEndRoundButtons,
                visible:false,
                wsButtonClicked:function () {
                    this.startNewRoundButton.visible = false;
                    this.toMainMenuButton.visible = false;

                    this.clearRoundResult();

                    if (this.typeOfRoom === 1) { // public
                        this.delegateOfGameScene.notifyServerIAmReady4NewRound();
                    } else if (this.typeOfRoom === 2) { // private
                        this.delegateOfGameScene.notifyServerIAmReady4NewRound();
                    } else { // ring
                        if (this.amIWinRound) {
                            this.delegateOfGameScene.notifyServerIAmReady4NewRound();
                        } else {
                            this.switchView2MatchingPlayers();
                            this.delegateOfGameScene.notifyServerOfRing();
                        }
                    }
                }.bind(this)
            }).addTo(parent);

            this.toMainMenuButton = this.asset.createMiddleButton({
                text:"退出",color:"black",wsTextHeight:this.asset.FIXED_HEIGHT_OF_MIDDLE_BUTTON/3,
                x:parent.width - gapBetweenEndRoundButtons - this.asset.FIXED_WIDTH_OF_MIDDLE_BUTTON,
                y:yPosOfEndRoundButtons,
                visible:false,
                wsButtonClicked:function () {
                    this.startNewRoundButton.visible = false;
                    this.toMainMenuButton.visible = false;

                    this.clearRoundResult();
                    this.delegateOfGameScene.notifyServerIWant2EndGame();
                    this.delegateOfGameScene.back2MainMenu();
                }.bind(this)
            }).addTo(parent);

            this.screenTouchInfoLabel = new FlickLabel({
                text:"点击屏幕开始摇骰子",
                color:"white",
                textAlign:"center",
                font:HEIGHT_OF_SCREEN_TOUCH_LABEL + "px 宋体",
                width:parent.width,
                maxWidth:parent.width,
                height:HEIGHT_OF_SCREEN_TOUCH_LABEL,
                x:0,y:yPosOfEndRoundButtons,
                visible:false
            }).addTo(parent);
        },

        switchView2MatchingPlayers:function (isPrivateRoom) {
            this.matchPlayerContainer.visible = true;
            this.roomContainer.visible = false;

            if (isPrivateRoom === true) {
                this.matchPlayerInformationText.text = "生成邀请链接"
            } else {
                this.matchPlayerInformationText.text = "正在匹配玩家"
            }
        },
        switchView2RoundStart:function () {
            this.matchPlayerContainer.visible = false;
            this.roomContainer.visible = true;
        },

        resetRoomByPlayers:function (players) {
            this.allPlayers = players;
            this.setCount2Guess(players.length);
            this.setSelectedManipulationDiceNumber(1);

            if (this.mapOfAllPlayerViews != null) {
                $.each(this.mapOfAllPlayerViews, function (k, pv) {
                    this.roomContainer.removeChild(pv);
                }.bind(this))
            }
            this.mapOfAllPlayerViews = {};

            var heightOfPlayerView = HEIGHT_OF_PLAYER_VIEW;
            var widthOfPlayerView = this.width - PADDING_AROUND_PLAYER_VIEW * 2;

            players.forEach(function (propertiesOfPlayer, index) {
                var xOfPlayerView = 0, yOfPlayerView = 0, rotationOfPlayerView = 0;
                var uuidOfPlayer = propertiesOfPlayer["uuid"];
                var pos = this.positionOfUUID(uuidOfPlayer);
                switch (pos) {
                    case "ME":
                        xOfPlayerView = (this.roomContainer.width - widthOfPlayerView) / 2;
                        yOfPlayerView = this.roomContainer.height - PADDING_AROUND_PLAYER_VIEW - heightOfPlayerView;
                        rotationOfPlayerView = 0;
                        break;
                    case "UP":
                        xOfPlayerView = (this.roomContainer.width - widthOfPlayerView) / 2;
                        yOfPlayerView = PADDING_AROUND_PLAYER_VIEW;
                        rotationOfPlayerView = 0;
                        break;
                    case "LEFT":
                        xOfPlayerView = PADDING_AROUND_PLAYER_VIEW;
                        yOfPlayerView = this.roomContainer.height/2 + widthOfPlayerView/2;
                        rotationOfPlayerView = -90;
                        break;
                    case "RIGHT":
                        xOfPlayerView = this.roomContainer.width - PADDING_AROUND_PLAYER_VIEW;
                        yOfPlayerView = this.roomContainer.height/2 - widthOfPlayerView/2;
                        rotationOfPlayerView = 90;
                        break;
                }

                this.mapOfAllPlayerViews[uuidOfPlayer] = new PlayerView($.extend(propertiesOfPlayer, {
                    width:widthOfPlayerView,
                    height:heightOfPlayerView,
                    x:xOfPlayerView,
                    y:yOfPlayerView,
                    rotation:rotationOfPlayerView,
                    asset:this.asset
                })).addTo(this.roomContainer);
            }.bind(this));
        },

        clearRoundResult:function () {
            this.countingLabel.visible = false;
            this.historyGuessView.visible = false;
            this.tellLiarLabel.visible = false;
        },

        positionOfUUID:function (uuid) {
            if (this.delegateOfGameScene.myUUID() === uuid) {
                return "ME";
            }

            if (this.allPlayers.length === 2) {
                return "UP";
            }

            var indexOfMe = this.orderOfPlayer(this.delegateOfGameScene.myUUID());
            var indexOfTarget = this.orderOfPlayer(uuid);

            if (indexOfMe === indexOfTarget) {
                return "ME";
            } else if ((indexOfMe + 1) % 4 === indexOfTarget) {
                return "RIGHT";
            } else if ((indexOfMe + 2) % 4 === indexOfTarget) {
                return "UP";
            } else {
                return "LEFT";
            }
        },

        orderOfPlayer:function (uuid) {
            for (var i = 0; i < this.allPlayers.length; i++) {
                if (this.allPlayers[i].uuid === uuid) {
                    return i;
                }
            }

            return -1;
        },

        setCount2Guess:function (number) {
            this.count2Guess = number;
            this.count2GuessLabel.text = number;
        },

        setSelectedManipulationDiceNumber:function(number) {
            this.factorManipulationButtons.forEach(function (button) {
                button.setSelected(false);
            });
            this.factorManipulationButtons[number - 1].setSelected(true);
        },

        getSelectedGuess:function () {
            var factor = 1;
            for (var i =0; i < this.factorManipulationButtons.length; i++) {
                if (this.factorManipulationButtons[i].isSelected()) {
                    factor = i + 1;
                    break;
                }
            }

            return {
                count:this.count2Guess,
                factor:factor
            }
        },

        playRoundAnimation:function(roundIndex) {
            this.roundInfoLabel.text = "Round " + roundIndex;
            this.roundInfoLabel.x = this.roomContainer.width/2;
            this.roundInfoLabel.y = -this.roomContainer.height/2;
            this.roundInfoLabel.visible = true;

            var originalAlpha = this.roundInfoLabel.alpha;
            var originalScaleX = this.roundInfoLabel.scaleX;
            var originalScaleY = this.roundInfoLabel.scaleY;

            Hilo.Tween.to(this.roundInfoLabel, {
                y:this.roomContainer.height/2
            }, {
                duration:500,
                onComplete:function () {

                    Hilo.Tween.to(this.roundInfoLabel, {
                        alpha:0,
                        scaleX:originalScaleX * 10,
                        scaleY:originalScaleY * 10
                    }, {
                        duration:1000,
                        delay:1500,
                        ease:Hilo.Ease.Quad.EaseIn,
                        onComplete:function () {
                            this.roundInfoLabel.alpha = originalAlpha;
                            this.roundInfoLabel.scaleX = originalScaleX;
                            this.roundInfoLabel.scaleY = originalScaleY;

                            this.roundInfoLabel.visible = false;

                            this.ready2Shake();
                        }.bind(this)
                    })
                }.bind(this)
            });
        },
        
        ready2Shake:function () {
            this.shakeDiceCup.visible = true;
            this.screenTouchInfoLabel.startFlick();
            this.screenTouchAcceptable = true;
        },

        startShake:function () {
            this.screenTouchInfoLabel.stopFlick();
            this.screenTouchAcceptable = false;
            this.shakeUpCup(true, 15);
        },

        shakeUpCup:function (isLeftDirection, timesLeft) {
            if (timesLeft > 0) {
                Hilo.Tween.to(this.shakeDiceCup, {
                    y:this.shakeDiceCup.y - 4,
                    rotation:isLeftDirection ? 22.5 : -22.5
                }, {
                    duration:100,
                    onComplete:function () {
                        this.shakeUpCup(!isLeftDirection, timesLeft - 1);
                    }.bind(this)
                })
            } else {
                Hilo.Tween.to(this.shakeDiceCup, {
                    rotation:0
                }, {
                    duration:50,
                    onComplete:function () {
                        Hilo.Tween.to(this.shakeDiceCup, {
                            y:this.roomContainer.height/2
                        }, {
                            duration:200,
                            onComplete:function () {
                                this.endShake();
                            }.bind(this)
                        })
                    }.bind(this)
                })
            }
        },
        
        endShake:function () {
            this.dicesITossed = this.randomDicesTossed();
            var dices = [];
            var widthOfDicesContainer = this.fiveDicesContainerAfterShake.width;
            var heightOfDicesContainer = this.fiveDicesContainerAfterShake.height;
            this.fiveDicesContainerAfterShake.removeAllChildren();

            for (var i = 0; i < this.dicesITossed.length; i++) {
                dices[i] = this.asset.createDiceImgByNumber({
                    number:this.dicesITossed[i],
                    x:0,y:0,width:widthOfDicesContainer,height:heightOfDicesContainer
                }).addTo(this.fiveDicesContainerAfterShake)
            }

            var myPlayerView = this.mapOfAllPlayerViews[this.delegateOfGameScene.myUUID()];
            var targetPositionOfFiveDices = myPlayerView.centerOfFiveDices().map(function (pos) {
                return {
                    x:myPlayerView.x + pos.x - this.fiveDicesContainerAfterShake.x,
                    y:myPlayerView.y + pos.y - this.fiveDicesContainerAfterShake.y
                }
            }.bind(this));
            var countOfDicesMovedToTargetPosition = 0;
            dices.forEach(function (dice, index) {
                Hilo.Tween.to(dice, {
                    x:targetPositionOfFiveDices[index].x,
                    y:targetPositionOfFiveDices[index].y
                }, {
                    duration:2000,
                    delay:500,
                    onComplete:function () {
                        countOfDicesMovedToTargetPosition++;
                        if (countOfDicesMovedToTargetPosition === dices.length) {
                            myPlayerView.setDices(this.dicesITossed);
                            this.fiveDicesContainerAfterShake.removeAllChildren();
                        }
                    }.bind(this)
                })
            }.bind(this));

            var originalXOfShakeDiceCup = this.shakeDiceCup.x;
            var originalYOfShakeDiceCup = this.shakeDiceCup.y;
            var originalScaleXOfShakeDiceCup = this.shakeDiceCup.scaleX;
            var originalScaleYOfShakeDiceCup = this.shakeDiceCup.scaleY;

            Hilo.Tween.to(this.shakeDiceCup, {
                x:originalXOfShakeDiceCup + this.roomContainer.width,
                y:originalYOfShakeDiceCup - this.roomContainer.width,
                scaleX:originalScaleXOfShakeDiceCup/2,
                scaleY:originalScaleYOfShakeDiceCup/2,
                rotation:90
            }, {
                duration:2000,
                delay:500,
                onComplete:function () {
                    this.shakeDiceCup.scaleX = originalScaleXOfShakeDiceCup;
                    this.shakeDiceCup.scaleY = originalScaleYOfShakeDiceCup;
                    this.shakeDiceCup.rotation = 0;
                    this.shakeDiceCup.x = originalXOfShakeDiceCup;
                    this.shakeDiceCup.y = originalYOfShakeDiceCup;
                    this.shakeDiceCup.visible = false;

                    this.ready2Guess();
                }.bind(this)
            });
        },

        ready2Guess:function () {
            this.myManipulationContainer.visible = true;
            this.sendMyGuessButton.setEnabled(false);
            this.pointOutLiarButton.setEnabled(false);

            this.delegateOfGameScene.notifyServerIHaveShakedDice();
        },

        ready2StartNewRound:function () {
            if (this.typeOfRoom === 4) { // ring
                if (this.amIWinRound) {
                    this.startNewRoundButton.setText("继续守擂");
                } else {
                    this.startNewRoundButton.setText("攻打新擂");
                }
            } else {
                this.startNewRoundButton.setText("新回合");
            }

            this.startNewRoundButton.visible = true;
            this.toMainMenuButton.visible = true;
        },

        afterResultDisplayAnimation:function () {
            this.ready2StartNewRound();
        },

        startTimerOfUUID:function (playerUUID) {
            var rotation = -180;
            switch (this.positionOfUUID(playerUUID)) {
                case "ME":
                    rotation = -180;break;
                case "UP":
                    rotation = 0;break;
                case "LEFT":
                    rotation = -90;break;
                case "RIGHT":
                    rotation = 90;break;
            }

            this.pointerImageView.rotation = rotation;
            this.pointerImageView.visible = true;

            this.mapOfAllPlayerViews[playerUUID].startCountDown();
        },

        stopTimerOfUUID:function (playerUUID) {
            this.pointerImageView.visible = false;
            this.mapOfAllPlayerViews[playerUUID].stopCountDown();
        },

        stopAllTimer:function () {
            $.each(this.mapOfAllPlayerViews, function (k, v) {
                v.stopCountDown();
            });
        },

        roundOver:function () {
            this.stopAllTimer();
        },

        setDicesByUUID:function (uuid, numbers) {
            var pv = this.mapOfAllPlayerViews[uuid];
            pv.setDices(numbers, true);
        },

        setStatusAsReadyByUUID:function (uuid) {
            var pv = this.mapOfAllPlayerViews[uuid];
            pv.showReady();
        },

        showGuessActionByUUID:function (uuid, guess) {
            this.historyGuessView.setGuess(guess.count, guess.factor);

            this.placeActionView(uuid, this.historyGuessView);
        },

        showNotBelieveActionByUUID:function (uuid) {
            this.placeActionView(uuid, this.tellLiarLabel);
        },

        placeActionView:function (uuid, view) {
            var widthOfPointer = this.pointerImageView.width;
            var heightOfPointer = this.pointerImageView.height;
            var centerXOfPointer = this.roomContainer.width/2;
            var centerYOfPointer = this.roomContainer.height/2;
            var leftOfPointer = centerXOfPointer-widthOfPointer/2;
            var rightOfPointer = centerXOfPointer+widthOfPointer/2;
            var topOfPointer = centerYOfPointer-heightOfPointer/2;
            var bottomOfPointer = centerYOfPointer+heightOfPointer/2;

            var gap2Pointer = view.height;

            switch (this.positionOfUUID(uuid)) {
                case "ME":
                    view.x = centerXOfPointer;
                    view.y = bottomOfPointer + gap2Pointer;
                    view.rotation = 0;
                    break;
                case "UP":
                    view.x = centerXOfPointer;
                    view.y = topOfPointer - gap2Pointer;
                    view.rotation = 0;
                    break;
                case "LEFT":
                    view.x = leftOfPointer - gap2Pointer;
                    view.y = centerYOfPointer;
                    view.rotation = 90;
                    break;
                case "RIGHT":
                    view.x = rightOfPointer + gap2Pointer;
                    view.y = centerYOfPointer;
                    view.rotation = -90;
                    break;
            }

            view.visible = true;
            ns.Asset.hideAndPopup(view);
        },

        displayRoundResult:function (result) {
            this.myManipulationContainer.visible = false;
            this.maniCountOfFactorContainer.visible = false;

            var allMatchedDices = [];

            var resultOfLoser = null, resultOfWinner = null;

            result.forEach(function (resultOfOnePlayer) {
                var playerUUID = resultOfOnePlayer.uuid;
                var dicesTossed = resultOfOnePlayer.matchedinforofdicestossed.map(function (el, index) {
                    return el.dicenumber;
                }.bind(this));

                if (playerUUID !== this.delegateOfGameScene.myUUID()) {
                    this.setDicesByUUID(playerUUID, dicesTossed);
                } else {
                    this.amIWinRound = resultOfOnePlayer.crownmodification > 0;
                }

                $.each(resultOfOnePlayer.matchedinforofdicestossed, function (index, el) {
                    if (el.matched) {
                        var dice = this.getDiceViewOfUUIDByIndex(playerUUID, index);
                        if (dice != null) {
                            allMatchedDices[allMatchedDices.length] = dice;
                        }
                    }
                }.bind(this));

                if (resultOfOnePlayer.crownmodification > 0) {
                    resultOfWinner = resultOfOnePlayer;
                }
                if (resultOfOnePlayer.crownmodification < 0) {
                    resultOfLoser = resultOfOnePlayer;
                }
            }.bind(this));

            ns.ticker.timeout(function () {
                this.countingLabel.visible = true;
                this.countingLabel.text = "0";

                ns.Asset.iterateBigAndSmall(allMatchedDices, function (view, index) {
                    this.countingLabel.text = index + 1;
                    view.background = "red";
                }.bind(this), function (view, index) {
                    // do nothing
                }.bind(this), function () {
                    if (resultOfLoser != null && resultOfWinner != null) {
                        this.moveCrown(resultOfLoser, resultOfWinner);
                    }

                    this.afterResultDisplayAnimation();
                }.bind(this))
            }.bind(this), 3000);
        },

        getDiceViewOfUUIDByIndex:function (uuid, indexOfDice) {
            var pv = this.mapOfAllPlayerViews[uuid];

            if (pv != null) {
                return pv.getDiceByIndex(indexOfDice);
            }

            return null;
        },

        getPlayerNameInRoomByUUID:function (uuid) {
            for (var i = 0; i < this.allPlayers.length; i++) {
                if (this.allPlayers[i].uuid === uuid) {
                    return this.allPlayers[i].playername;
                }
            }

            return null;
        },

        moveCrown:function(fromLoser, toWinner) {
            var uuidOfLoser = fromLoser.uuid;
            var crownModificationOfLoser = fromLoser.crownmodification;
            var theLoserView = this.mapOfAllPlayerViews[uuidOfLoser];

            var uuidOfWinner = toWinner.uuid;
            var crownModificationOfWinner = toWinner.crownmodification;
            var theWinnerView = this.mapOfAllPlayerViews[uuidOfWinner];

            if (theLoserView == null || theWinnerView == null) {
                return;
            }

            theLoserView.modifyCountOfCrown(crownModificationOfLoser);

            var startFrameOfCrownMoving = theLoserView.frameOfCrown();
            var endFrameOfCrownMoving = theWinnerView.frameOfCrown();

            var startCenterPoint = ns.Asset.convertPoint({
                x:startFrameOfCrownMoving.x + startFrameOfCrownMoving.width/2,
                y:startFrameOfCrownMoving.y + startFrameOfCrownMoving.height/2
            }, theLoserView, theLoserView.rotation);
            var endCenterPoint = ns.Asset.convertPoint({
                x:endFrameOfCrownMoving.x + endFrameOfCrownMoving.width/2,
                y:endFrameOfCrownMoving.y + endFrameOfCrownMoving.height/2
            }, theWinnerView, theWinnerView.rotation);

            var crownMoving = this.asset.createCrownImg({
                x:startCenterPoint.x,
                y:startCenterPoint.y,
                rotation:theLoserView.rotation,
                width:startFrameOfCrownMoving.width,
                height:startFrameOfCrownMoving.height,
                pivotX:startFrameOfCrownMoving.width/2,
                pivotY:startFrameOfCrownMoving.height/2
            }).addTo(this.roomContainer);

            var originalScaleXOfCrownMoving = crownMoving.scaleX;
            var originalScaleYOfCrownMoving = crownMoving.scaleY;

            Hilo.Tween.to(crownMoving, {
                x:this.roomContainer.width/2 + crownMoving.width/2,
                y:this.roomContainer.height/2 + crownMoving.height/2,
                rotation:0,
                scaleX:originalScaleXOfCrownMoving*5,
                scaleY:originalScaleYOfCrownMoving*5
            }, {
                duration:2000,
                onComplete:function () {
                    theWinnerView.modifyCountOfCrown(crownModificationOfWinner);

                    Hilo.Tween.to(crownMoving, {
                        x:endCenterPoint.x,
                        y:endCenterPoint.y,
                        rotation:theWinnerView.rotation,
                        scaleX:originalScaleXOfCrownMoving,
                        scaleY:originalScaleYOfCrownMoving
                    }, {
                        duration:1000,
                        onComplete:function () {
                            this.roomContainer.removeChild(crownMoving);
                        }.bind(this)
                    })
                }.bind(this)
            })
        },
        
        randomDicesTossed:function () {
            return [
                Math.floor((Math.random()*6)+1),
                Math.floor((Math.random()*6)+1),
                Math.floor((Math.random()*6)+1),
                Math.floor((Math.random()*6)+1),
                Math.floor((Math.random()*6)+1)
            ]
        },

        /*
         * Be Notified From Poll
         */
        beNotifiedOfMyRoomID:function (roomid, typeOfRoom) {
            this.typeOfRoom = typeOfRoom;
            if (this.typeOfRoom === 2) {
                this.matchPlayerInformationText.text = "房间号:" + roomid;
            } else {
                this.matchPlayerInformationText.text = "正在匹配玩家";
            }
        },
        beNotified2StartRound:function(roundIndex, myCards, playersInRoom) {
            this.resetRoomByPlayers(playersInRoom);
            this.playRoundAnimation(roundIndex);
        },
        beNotifiedOfCardUsed:function (typeOfCard, sourceUUID, targetUUIDArray) {

        },
        beNotifiedOfMyCard2UseNotAvailable:function (message) {

        },
        beNotifiedOfOneClientHasShakedDice:function (playerIDWhoShakedDice) {
            if (playerIDWhoShakedDice !== this.delegateOfGameScene.myUUID()) {
                this.setDicesByUUID(playerIDWhoShakedDice, FIVE_UNKNOW_DICES);
            }
        },
        beNotifiedOfOneClient2Guess:function (playerID2GuessDice) {
            if (playerID2GuessDice !== this.delegateOfGameScene.myUUID()) {
                this.maniCountOfFactorContainer.visible = false;
                this.sendMyGuessButton.setEnabled(false);
            } else {
                this.maniCountOfFactorContainer.visible = true;
                this.sendMyGuessButton.setEnabled(true);
            }

            this.startTimerOfUUID(playerID2GuessDice);
        },
        beNotifiedOfNotMyTurn2Guess:function () {
            var alertView = this.createAlertView({
                wsMessage:"没轮到你猜呢",
                wsOKHandler:function () {
                    this.removeChild(alertView);
                }.bind(this)
            });

            alertView.visible = true;
        },
        beNotifiedOfNotTime2PointOutLiar:function () {
            var alertView = this.createAlertView({
                wsMessage:"现在你还不能质疑",
                wsOKHandler:function () {
                    this.removeChild(alertView);
                }.bind(this)
            });

            alertView.visible = true;
        },
        beNotifiedOfMyLastGuessIsInvalid:function (invalidMessage) {
            this.sendMyGuessButton.setEnabled(true);
            this.pointOutLiarButton.setEnabled(true);

            var alertView = this.createAlertView({
                wsMessage:invalidMessage,
                wsOKHandler:function () {
                    this.removeChild(alertView);
                }.bind(this)
            });

            alertView.visible = true;
        },
        beNotifiedOfGuessByPlayer:function (guess, playerUUID, nextPlayerUUID) {
            if (guess.factor === 1) {
                this.oneHasBeenGuessed = true;
            }

            var isMyGuess = playerUUID === this.delegateOfGameScene.myUUID();
            this.pointOutLiarButton.setEnabled(!isMyGuess);

            this.setCount2Guess(guess.count);
            this.setSelectedManipulationDiceNumber(guess.factor);

            this.showGuessActionByUUID(playerUUID, guess);

            this.stopTimerOfUUID(playerUUID);
            this.beNotifiedOfOneClient2Guess(nextPlayerUUID);
        },
        beNotified2OpenCup:function (uuidOfNotBelieveGuy) {
            this.showNotBelieveActionByUUID(uuidOfNotBelieveGuy);

            this.stopTimerOfUUID(uuidOfNotBelieveGuy);
            this.roundOver();

            this.delegateOfGameScene.notifyServerMyDicesShaked(this.dicesITossed)
        },
        beNotifiedOfRoundResult:function (result) {
            this.displayRoundResult(result);
        },
        beNotifiedOfOneClientIsReady4NewRound:function (playerUUID) {
            this.setStatusAsReadyByUUID(playerUUID);
        },
        beNotified2EndGameOfServerCrashed:function () {
            var alertView = this.createAlertView({
                wsMessage:"服务器崩溃啦",
                wsOKHandler:function () {
                    this.removeChild(alertView);
                    this.delegateOfGameScene.back2MainMenu();
                }.bind(this)
            });

            alertView.visible = true;
        },
        beNotified2EndGameOfSomeoneLostConnectionFromServer:function (playerUUID) {
            this.__EndGameOfSomeone__(playerUUID, "失去了连接");
        },
        beNotified2EndGameOfSomeoneAsk2ExitGame:function (playerUUID) {
            this.__EndGameOfSomeone__(playerUUID, "退出了游戏");
        },

        __EndGameOfSomeone__:function (playerUUID, message) {
            if (this.delegateOfGameScene.myUUID() === playerUUID) {
                this.delegateOfGameScene.back2MainMenu();
            } else {
                var playerName = this.getPlayerNameInRoomByUUID(playerUUID);
                if (playerName === null) {
                    return;
                }

                var alertView = this.createAlertView({
                    wsMessage:playerName + message,
                    wsOKHandler:function () {
                        this.removeChild(alertView);
                        this.delegateOfGameScene.back2MainMenu();
                    }.bind(this)
                });

                alertView.visible = true;
            }
        }
    });

    var PlayerView = Hilo.Class.create({
        Extends : Hilo.Container,
        asset:null,
        fiveDicesContainer:null,
        fiveDices:[],
        countOfCrownText:null,
        countDownText:null,
        readyGoImg:null,
        crownImg:null,

        timer:null,
        countDownSecond:null,
        countOfCrown:null,

        constructor:function (properties) {
            PlayerView.superclass.constructor.call(this, properties);
            this.init(properties);
        },

        init:function (properties) {
            this.asset = properties.asset;

            this.background = "rgba(255,255,255,0.5)";

            var widthOfFiveDicesContainer = SIZE_OF_DICE * 5 + PADDING_BETWEEN_DICES * 4;
            this.fiveDicesContainer = new Hilo.Container({
                x:this.width-widthOfFiveDicesContainer-PADDING_INSIDE_PLAYER_VIEW,
                y:(this.height-SIZE_OF_DICE)/2,
                width:widthOfFiveDicesContainer,
                height:SIZE_OF_DICE
            }).addTo(this);

            var figureImage = new Hilo.Bitmap({
                image:properties.figure.path,
                x:PADDING_INSIDE_PLAYER_VIEW,
                y:(this.height-SIZE_OF_FIGURE_IMAGE)/2,
                width:SIZE_OF_FIGURE_IMAGE,
                height:SIZE_OF_FIGURE_IMAGE
            }).addTo(this);

            this.readyGoImg = this.asset.createReadyGoImg({
                x:-PADDING_BETWEEN_WIDGETS_INSIDE_PLAYER_VIEW,
                y:-PADDING_BETWEEN_WIDGETS_INSIDE_PLAYER_VIEW,
                width:SIZE_OF_ACTION_IMAGE,
                height:SIZE_OF_ACTION_IMAGE,
                visible:false
            }).addTo(this);

            var rightOfFigureImage = figureImage.x + figureImage.width;
            var nameLabel = new Hilo.Text({
                text:properties.playername,
                font:HEIGHT_OF_NAME_LABEL + "px 宋体",
                color:"white",
                x:rightOfFigureImage + PADDING_BETWEEN_WIDGETS_INSIDE_PLAYER_VIEW,
                y:PADDING_INSIDE_PLAYER_VIEW,
                width:this.fiveDicesContainer.x - PADDING_BETWEEN_WIDGETS_INSIDE_PLAYER_VIEW - rightOfFigureImage,
                height:HEIGHT_OF_NAME_LABEL
            }).addTo(this);

            this.crownImg = this.asset.createCrownImg({
                x:rightOfFigureImage + PADDING_BETWEEN_WIDGETS_INSIDE_PLAYER_VIEW,
                y:this.height - PADDING_INSIDE_PLAYER_VIEW - SIZE_OF_CROWN,
                width:SIZE_OF_CROWN,
                height:SIZE_OF_CROWN
            }).addTo(this);
            var rightOfCrownImg = this.crownImg.x + this.crownImg.width;

            this.countOfCrownText = new Hilo.Text({
                color:"white",
                font:HEIGHT_OF_NAME_LABEL + "px 宋体",
                x:rightOfCrownImg + PADDING_BETWEEN_WIDGETS_INSIDE_PLAYER_VIEW,
                y:this.crownImg.y + SIZE_OF_CROWN - HEIGHT_OF_NAME_LABEL,
                width:this.fiveDicesContainer.x - PADDING_BETWEEN_WIDGETS_INSIDE_PLAYER_VIEW - rightOfCrownImg,
                height:HEIGHT_OF_NAME_LABEL
            }).addTo(this);

            this.countDownText = new Hilo.Text({
                text:"15",
                color:"white",
                font:HEIGHT_OF_NAME_LABEL + "px 宋体",
                x:-PADDING_BETWEEN_WIDGETS_INSIDE_PLAYER_VIEW,
                y:-PADDING_BETWEEN_WIDGETS_INSIDE_PLAYER_VIEW,
                height:HEIGHT_OF_NAME_LABEL,
                visible:false
            }).addTo(this);

            this.setCountOfCrown(properties.countofallcrowns);
        },

        setDices:function(numbers, animation) {
            this.fiveDicesContainer.removeAllChildren();
            this.dices = [];

            for (var i = 0; i < 5; i++) {
                var newDice;
                if (numbers[i] === 0) {
                    newDice = this.asset.createDiceImgOfQuestion({
                        width:SIZE_OF_DICE, height:SIZE_OF_DICE, x:(SIZE_OF_DICE + PADDING_BETWEEN_DICES) * i + SIZE_OF_DICE/2, y:SIZE_OF_DICE/2,
                        pivotX:SIZE_OF_DICE/2, pivotY:SIZE_OF_DICE/2
                    }).addTo(this.fiveDicesContainer);
                } else {
                    newDice = this.asset.createDiceImgByNumber({
                        number:numbers[i],
                        width:SIZE_OF_DICE, height:SIZE_OF_DICE, x:(SIZE_OF_DICE + PADDING_BETWEEN_DICES) * i + SIZE_OF_DICE/2, y:SIZE_OF_DICE/2,
                        pivotX:SIZE_OF_DICE/2, pivotY:SIZE_OF_DICE/2
                    }).addTo(this.fiveDicesContainer)
                }

                this.dices[this.dices.length] = newDice;

                if (animation === true) {
                    ns.Asset.hideAndPopup(newDice);
                }
            }
        },

        getDiceByIndex:function (index) {
            return this.dices[index];
        },

        centerOfFiveDices:function () {
            return [{
                x:this.fiveDicesContainer.x + SIZE_OF_DICE/2,
                y:this.fiveDicesContainer.y + SIZE_OF_DICE/2
            }, {
                x:this.fiveDicesContainer.x + PADDING_BETWEEN_DICES + SIZE_OF_DICE*3/2,
                y:this.fiveDicesContainer.y + SIZE_OF_DICE/2
            }, {
                x:this.fiveDicesContainer.x + PADDING_BETWEEN_DICES*2 + SIZE_OF_DICE*5/2,
                y:this.fiveDicesContainer.y + SIZE_OF_DICE/2
            }, {
                x:this.fiveDicesContainer.x + PADDING_BETWEEN_DICES*3 + SIZE_OF_DICE*7/2,
                y:this.fiveDicesContainer.y + SIZE_OF_DICE/2
            }, {
                x:this.fiveDicesContainer.x + PADDING_BETWEEN_DICES*4 + SIZE_OF_DICE*9/2,
                y:this.fiveDicesContainer.y + SIZE_OF_DICE/2
            }]
        },

        frameOfCrown:function () {
            return {
                x:this.crownImg.x,
                y:this.crownImg.y,
                width:this.crownImg.width,
                height:this.crownImg.height
            }
        },

        startCountDown:function () {
            this.countDownText.visible = true;
            this.setCountDownSecond(15);
            this.timer = new Hilo.Ticker();
            this.timer.interval(function () {
                this.updateCountDownSecond();
            }.bind(this), 1000);
            this.timer.start();
        },

        setCountDownSecond:function (number) {
            this.countDownSecond = number;
            this.countDownText.text = number;
        },

        updateCountDownSecond:function () {
            if (this.countDownSecond > 0) {
                this.setCountDownSecond(this.countDownSecond - 1);
            }
        },
        
        stopCountDown:function () {
            this.countDownText.text = "";
            this.countDownText.visible = false;
            if (this.timer != null) {
                this.timer.stop();
                this.timer = null;
            }
        },

        setCountOfCrown:function (newCount) {
            this.countOfCrown = newCount;
            this.countOfCrownText.text = newCount;
        },

        modifyCountOfCrown:function (modification) {
            if (modification === 0) {
                return;
            }

            var textColor, fromY, toY;
            if (modification > 0) {
                textColor = "red";
                fromY = this.countOfCrownText.y - this.countOfCrownText.height*2;
                toY = this.countOfCrownText.y;
            } else {
                textColor = "green";
                fromY = this.countOfCrownText.y;
                toY = this.countOfCrownText.y - this.countOfCrownText.height*2;
            }

            var modificationLabel = new Hilo.Text({
                font:HEIGHT_OF_NAME_LABEL + "px 宋体",
                color:textColor,
                text:modification,
                x:this.countOfCrownText.x,
                y:fromY,
                width:this.countOfCrownText.width,
                height:this.countOfCrownText.height
            }).addTo(this);

            Hilo.Tween.to(modificationLabel, {
                y:toY
            }, {
                duration:1000,
                onComplete:function () {
                    this.removeChild(modificationLabel);
                    this.setCountOfCrown(this.countOfCrown + modification);
                }.bind(this)
            })
        },

        showReady:function () {
            this.readyGoImg.visible = true;
        }
    });

    var GuessView = Hilo.Class.create({
        Extends:Hilo.Container,
        asset:null,

        countLabel:null,
        diceImageView:null,

        constructor:function (properties) {
            GuessView.superclass.constructor.call(this, properties);
            this.init(properties)
        },
        init:function (properties) {
            this.asset = properties["asset"];

            this.countLabel = new Hilo.Text({
                height:SIZE_OF_DICE/3*2,width:SIZE_OF_DICE*2,x:0,y:SIZE_OF_DICE/6,
                font:SIZE_OF_DICE/3*2 + "px 宋体",
                textAlign:"center",
                color:"white",
                text:"10个"
            }).addTo(this);

            this.diceImageView = this.asset.createDiceImgOfQuestion({
                height:SIZE_OF_DICE,width:SIZE_OF_DICE,x:SIZE_OF_DICE*2,y:0
            }).addTo(this);
        },

        setGuess:function(count, number) {
            this.countLabel.text = count + "个";

            this.diceImageView.removeFromParent();
            this.diceImageView = this.asset.createDiceImgByNumber({
                number:number,
                height:SIZE_OF_DICE,width:SIZE_OF_DICE,x:SIZE_OF_DICE*2,y:0
            }).addTo(this);
        }
    });



    var SelectableDiceButton = Hilo.Class.create({
        Extends:Hilo.Container,

        selectedBg:null,

        constructor:function (properties) {
            SelectableDiceButton.superclass.constructor.call(this, properties);

            this.init(properties);
        },

        /*
         * asset
         * number
         */
        init:function (properties) {
            var asset = properties["asset"];

            this.selectedBg = asset.createSelectedBg($.extend(properties, {
                x:0,y:0,visible:false
            })).addTo(this);
            asset.createDiceImgByNumber($.extend(properties, {
                x:0,y:0,visible:true
            })).addTo(this);

            this.on(Hilo.event.POINTER_END, function (e) {
                properties["wsButtonClicked"].call(this, properties["number"]);
            }.bind(this));
        },

        isSelected:function () {
            return this.selectedBg.visible;
        },

        setSelected:function(b) {
            this.selectedBg.visible = b === true;
        }
    });

    var FlickLabel = Hilo.Class.create({
        Extends:Hilo.Text,

        isFlicking:false,

        constructor:function(properties) {
            FlickLabel.superclass.constructor.call(this, properties)
        },
        
        startFlick:function () {
            this.isFlicking = true;
            this.visible = true;
            this.fadeInAndOut();
        },
        
        stopFlick:function () {
            this.isFlicking = false;
            this.alpha = 0;
            this.visible = false;
        },
        
        fadeInAndOut:function () {
            var targetAlpha = 1;
            if (this.alpha === 1) {
                targetAlpha = 0.3;
            }

            Hilo.Tween.to(this, {
                alpha:targetAlpha
            }, {
                duration: 1000,
                onComplete: function () {
                    if (this.isFlicking) {
                        this.fadeInAndOut();
                    }
                }.bind(this)
            });
        }
    });
})(window.game);