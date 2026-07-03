(function(ns) {
    var Asset = ns.Asset = Hilo.Class.create({
        Mixes: Hilo.EventMixin,

        queue:null,

        bg:null,
        buttons:null,
        dices:null,
        materials:null,

        FIXED_HEIGHT_OF_MIDDLE_BUTTON:80,
        FIXED_WIDTH_OF_MIDDLE_BUTTON:240,

        load:function() {
            var resources = [
                {id:"bg", src:"images/background_1920_1080.jpg"},
                {id:"buttons", src:"images/buttons.png"},
                {id:"dices", src:"images/dices.png"},
                {id:"materials",src:"images/materials.png"}
            ];

            this.queue = new Hilo.LoadQueue();
            this.queue.add(resources);
            this.queue.on("complete", this.onComplete.bind(this));
            this.queue.start();
        },

        onComplete:function() {
            this.bg = this.queue.get("bg").content;
            this.buttons = this.queue.get("buttons").content;
            this.dices = this.queue.get("dices").content;
            this.materials = this.queue.get("materials").content;

            this.queue.off("complete");
            this.fire("complete")
        },

        createBigButton:function (properties) {
            var insidebutton = new Hilo.Button($.extend($.extend({}, properties), {
                x:0,y:0,
                image:this.buttons,
                upState:{"rect":[0,0,240,160]},
                disabledState:{"rect":[240,0,240,160]},
                downState:{"rect":[480,0,240,160]}
            }));

            return new TextButton($.extend(properties, {
                "wsInsideButton":insidebutton
            }));
        },

        createMiddleButton:function (properties) {
            var prop = $.extend($.extend({}, properties), {
                width:this.FIXED_WIDTH_OF_MIDDLE_BUTTON,
                height:this.FIXED_HEIGHT_OF_MIDDLE_BUTTON
            });

            var insidebutton = new Hilo.Button($.extend($.extend({}, prop), {
                x:0,y:0,
                image:this.buttons,
                upState:{"rect":[0,160,240,80]},
                disabledState:{"rect":[240,160,240,80]},
                downState:{"rect":[480,160,240,80]},
                visible:true
            }));

            return new TextButton($.extend(prop, {
                "wsInsideButton":insidebutton
            }));
        },
        createRedButton:function (properties) {
            var prop = $.extend($.extend({}, properties), {
                width:this.FIXED_WIDTH_OF_MIDDLE_BUTTON,
                height:this.FIXED_HEIGHT_OF_MIDDLE_BUTTON
            });

            var insidebutton = new Hilo.Button($.extend($.extend({}, prop), {
                x:0,y:0,
                image:this.buttons,
                upState:{"rect":[0,240,240,80]},
                disabledState:{"rect":[240,240,240,80]},
                downState:{"rect":[480,240,240,80]}
            }));

            return new TextButton($.extend(prop, {
                "wsInsideButton":insidebutton
            }));
        },
        createGreenButton:function (properties) {
            var prop = $.extend($.extend({}, properties), {
                width:this.FIXED_WIDTH_OF_MIDDLE_BUTTON,
                height:this.FIXED_HEIGHT_OF_MIDDLE_BUTTON
            });

            var insidebutton = new Hilo.Button($.extend($.extend({}, prop), {
                x:0,y:0,
                image:this.buttons,
                upState:{"rect":[0,320,240,80]},
                disabledState:{"rect":[240,320,240,80]},
                downState:{"rect":[480,320,240,80]}
            }));

            return new TextButton($.extend(prop, {
                "wsInsideButton":insidebutton
            }));
        },

        createDiceImgByNumber:function(properties) {
            return new Hilo.Bitmap($.extend(properties, {
                image:this.dices,
                rect:[85 * properties["number"], 0, 85, 85]
            }));
        },
        createDiceImgOfFlexiable:function(properties) {
            return new Hilo.Bitmap($.extend(properties, {
                image:this.dices,
                rect:[595, 0, 85, 85]
            }));
        },
        createDiceImgOfQuestion:function(properties) {
            return new Hilo.Bitmap($.extend(properties, {
                image:this.dices,
                rect:[0, 0, 85, 85]
            }));
        },
        createSelectedBg:function (properties) {
            return new Hilo.Bitmap($.extend(properties, {
                image:this.dices,
                rect:[680, 0, 85, 85]
            }))
        },

        createCrownImg:function (properties) {
            return new Hilo.Bitmap($.extend(properties, {
                image:this.materials,
                rect:[0, 0, 128, 128]
            }));
        },
        createReadyGoImg:function (properties) {
            return new Hilo.Bitmap($.extend(properties, {
                image:this.materials,
                rect:[128, 0, 32, 32]
            }));
        },
        createMinusImg:function (properties) {
            return new Hilo.Bitmap($.extend(properties, {
                image:this.materials,
                rect:[200, 0, 40, 40]
            }));
        },
        createPlusImg:function (properties) {
            return new Hilo.Bitmap($.extend(properties, {
                image:this.materials,
                rect:[160, 0, 40, 40]
            }));
        },
        createDiceCupImg:function (properties) {
            return new Hilo.Bitmap($.extend(properties, {
                image:this.materials,
                rect:[0, 128, 225, 225]
            }));
        },
        createPointerImg:function (properties) {
            return new Hilo.Bitmap($.extend(properties, {
                image:this.materials,
                rect:[225, 213, 140, 140]
            }));
        }
    });

    var TextButton = Hilo.Class.create({
        Extends:Hilo.Container,
        constructor:function (properties) {
            TextButton.superclass.constructor.call(this, properties);

            this.init(properties);
        },

        insideText:null,
        insideButton:null,

        init:function (properties) {
            this.insideButton = properties["wsInsideButton"].addTo(this);

            var textHeight = properties["wsTextHeight"];
            this.insideText = new Hilo.Text($.extend($.extend({}, properties), {
                x:0,y:(this.height-textHeight)/2,width:this.width,height:textHeight,
                maxWidth:this.width,
                font:textHeight + "px 宋体",
                textAlign:"center",
                visible:true
            })).addTo(this);

            if ($.isFunction(properties["wsButtonClicked"])) {
                this.on(Hilo.event.POINTER_END, function (e) {
                    if (this.insideButton.enabled) {
                        properties["wsButtonClicked"]();
                    }
                })
            }
        },

        setText:function (newText) {
            this.insideText.text = newText;
        },

        setEnabled:function (b) {
            this.insideButton.setEnabled(b);
        }
    });

    $.extend(ns.Asset, {
        hideAndPopup:function (view) {
            var originalScaleX = view.scaleX;
            var originalScaleY = view.scaleY;

            view.scaleX = originalScaleX * 0.01;
            view.scaleY = originalScaleY * 0.01;

            Hilo.Tween.to(view, {
                scaleX:originalScaleX * 1.1,
                scaleY:originalScaleY * 1.1
            }, {
                duration:300,
                onComplete:function () {
                    Hilo.Tween.to(view, {
                        scaleX:originalScaleX * 0.9,
                        scaleY:originalScaleY * 0.9
                    }, {
                        duration:100,
                        onComplete:function () {
                            Hilo.Tween.to(view, {
                                scaleX:originalScaleX*1.05,
                                scaleY:originalScaleY*1.05
                            }, {
                                duration:100,
                                onComplete:function () {
                                    Hilo.Tween.to(view, {
                                        scaleX:originalScaleX*0.95,
                                        scaleY:originalScaleY*0.95
                                    }, {
                                        duration:100,
                                        onComplete:function () {
                                            Hilo.Tween.to(view, {
                                                scaleX:originalScaleX,
                                                scaleY:originalScaleY
                                            }, {
                                                duration:100
                                            })
                                        }.bind(this)
                                    })
                                }.bind(this)
                            })
                        }.bind(this)
                    })
                }.bind(this)
            })
        },

        convertPoint:function (insidePoint, parentPoint, parentRotation) {
            var res;
            if (parentRotation === 90) {
                res = {
                    x:parentPoint.x - insidePoint.y,
                    y:parentPoint.y + insidePoint.x
                }
            } else if (parentRotation === -90) {
                res = {
                    x:parentPoint.x + insidePoint.y,
                    y:parentPoint.y - insidePoint.x
                }
            } else {
                res = {
                    x:parentPoint.x + insidePoint.x,
                    y:parentPoint.y + insidePoint.y
                }
            }

            return res;
        },

        iterateBigAndSmall:function (allViews, callbackOnEachStart, callbackOnEachFinished, callbackOnAllFinished) {
            ns.Asset.__IterateBigAndSmallByIndex(allViews, 0, callbackOnEachStart, callbackOnEachFinished, callbackOnAllFinished)
        },

        __IterateBigAndSmallByIndex:function (allViews, currentIndex, callbackOnCurrentIndex2Start, callbackOnCurrentIndexFinished, callbackOnIndexOutOfRange) {
            if (currentIndex >= 0 && currentIndex < allViews.length) {
                callbackOnCurrentIndex2Start(allViews[currentIndex], currentIndex);

                ns.Asset.bigAndSmall(allViews[currentIndex], function () {
                    callbackOnCurrentIndexFinished(allViews[currentIndex], currentIndex);

                    ns.Asset.__IterateBigAndSmallByIndex(allViews, currentIndex + 1, callbackOnCurrentIndex2Start, callbackOnCurrentIndexFinished, callbackOnIndexOutOfRange);
                });
            } else {
                callbackOnIndexOutOfRange();
            }
        },

        bigAndSmall:function(view, callback) {
            var originalScaleX = view.scaleX;
            var originalScaleY = view.scaleY;

            Hilo.Tween.to(view, {
                scaleX:originalScaleX * 1.5,
                scaleY:originalScaleY * 1.5
            }, {
                duration:300,
                onComplete:function () {
                    Hilo.Tween.to(view, {
                        scaleX:originalScaleX * 0.9,
                        scaleY:originalScaleY * 0.9
                    }, {
                        duration:100,
                        onComplete:function () {
                            Hilo.Tween.to(view, {
                                scaleX:originalScaleX*1.05,
                                scaleY:originalScaleY*1.05
                            }, {
                                duration:100,
                                onComplete:function () {
                                    Hilo.Tween.to(view, {
                                        scaleX:originalScaleX*0.95,
                                        scaleY:originalScaleY*0.95
                                    }, {
                                        duration:100,
                                        onComplete:function () {
                                            Hilo.Tween.to(view, {
                                                scaleX:originalScaleX,
                                                scaleY:originalScaleY
                                            }, {
                                                duration:100,
                                                onComplete:function () {
                                                    callback();
                                                }
                                            })
                                        }.bind(this)
                                    })
                                }.bind(this)
                            })
                        }.bind(this)
                    })
                }.bind(this)
            })
        }
    });

    var Scene = ns.Scene = Hilo.Class.create({
        Extends : Hilo.Container,
        constructor : function (properties) {
            Scene.superclass.constructor.call(this, properties);

            this.asset = properties["wsAsset"];
        },

        asset:null,

        /*
         * wsMessage
         * wsOKHandler
         */
        createAlertView:function (properties) {
            var mask = new Hilo.Container({
                x:0,y:0,width:this.width,height:this.height,background:"rgba(255,255,255,0.5)",
                visible:false
            }).addTo(this);

            var container = new Hilo.Container({
                pivotX:this.width/2,
                pivotY:200,
                width:this.width,
                height:400,
                x:this.width/2,
                y:this.height/2,
                background:"gray"
            }).addTo(mask);

            var sizeOfText = 40;
            var gapBetweenTextAndButton = 80;

            new Hilo.Text({
                text:properties["wsMessage"],
                width:container.width,
                height:sizeOfText,
                x:0,
                y:container.height/2 - sizeOfText - gapBetweenTextAndButton/2,
                font:sizeOfText + "px 宋体",
                color:"white",
                textAlign:"center",
                maxWidth:container.width
            }).addTo(container);

            this.asset.createMiddleButton({
                x:container.width/2 - this.asset.FIXED_WIDTH_OF_MIDDLE_BUTTON/2,
                y:container.height/2 + gapBetweenTextAndButton/2,
                text:"确定",
                wsTextHeight:this.asset.FIXED_HEIGHT_OF_MIDDLE_BUTTON/3,
                wsButtonClicked:function () {
                    $.isFunction(properties["wsOKHandler"]) && properties["wsOKHandler"]()
                }
            }).addTo(container);

            return mask;
        },

        createPromptView:function (properties) {
            var mask = new Hilo.Container({
                x:0,y:0,width:this.width,height:this.height,background:"rgba(255,255,255,0.5)",
                visible:false
            }).addTo(this);

            var container = new Hilo.Container({
                pivotX:this.width/2,
                pivotY:200,
                width:this.width,
                height:400,
                x:this.width/2,
                y:this.height/2,
                background:"gray"
            }).addTo(mask);

            var sizeOfText = 40;

            new Hilo.DOMElement({
                element:Hilo.createElement("input", {
                    type:"text",
                    style:{
                        "font-size":sizeOfText + "px"
                    }
                }),
                width:container.width,
                height:40,
                scaleX:0.5,
                scaleY:0.5,
                x:20,
                y:100
            }).addTo(container);

            new Hilo.Text({
                text:properties["wsMessage"],
                width:container.width,
                height:sizeOfText,
                x:0,
                y:container.height/2 - sizeOfText,
                font:sizeOfText + "px 宋体",
                color:"white",
                textAlign:"center",
                maxWidth:container.width
            }).addTo(container);

            var cancelButton = this.asset.createMiddleButton({
                x:container.width/3-this.asset.FIXED_WIDTH_OF_MIDDLE_BUTTON/2,
                y:container.height-this.asset.FIXED_HEIGHT_OF_MIDDLE_BUTTON,
                text:"取消",
                wsTextHeight:this.asset.FIXED_HEIGHT_OF_MIDDLE_BUTTON/3
            }).addTo(container);

            var ensureButton = this.asset.createMiddleButton({
                x:container.width/3*2-this.asset.FIXED_WIDTH_OF_MIDDLE_BUTTON/2,
                y:container.height-this.asset.FIXED_HEIGHT_OF_MIDDLE_BUTTON,
                text:"确定",
                wsTextHeight:this.asset.FIXED_HEIGHT_OF_MIDDLE_BUTTON/3
            }).addTo(container);

            return mask;
        }
    });
})(window.game);