// Learn cc.Class:
//  - [Chinese] https://docs.cocos.com/creator/manual/zh/scripting/class.html
//  - [English] http://docs.cocos2d-x.org/creator/manual/en/scripting/class.html
// Learn Attribute:
//  - [Chinese] https://docs.cocos.com/creator/manual/zh/scripting/reference/attributes.html
//  - [English] http://docs.cocos2d-x.org/creator/manual/en/scripting/reference/attributes.html
// Learn life-cycle callbacks:
//  - [Chinese] https://docs.cocos.com/creator/manual/zh/scripting/life-cycle-callbacks.html
//  - [English] https://www.cocos2d-x.org/docs/creator/manual/en/scripting/life-cycle-callbacks.html

var lg = require('login.js')

cc.Class({
    extends: cc.Component,

    properties: {
        sceneLayer:{
            default:null,
            type:cc.Node
        },
        popupLayer:{
            default:null,
            type:cc.Node
        },
        quickStartButton : {
            default:null,
            type:cc.Button
        }
    },

    // LIFE-CYCLE CALLBACKS:

    // onLoad () {},

    start () {
        var buttonLabel = this.quickStartButton.node.getChildByName("Background").getChildByName("Label").getComponent(cc.Label)
        buttonLabel.string = "HelloWorld"

        var newNode = new cc.Node()
        this.sceneLayer.addChild(newNode)
        newNode.setPosition(cc.v2(300, 200))
        newNode.setContentSize(cc.size(160, 80))
        newNode.color = cc.Color.RED
        newNode.anchorX = 0
        newNode.anchorY = 0

        var newLabel = newNode.addComponent(cc.Label)
        newLabel.string = "i am new label"

        // var ls = new lg.LoginScene();
        // this.popupLayer.addChild(ls.node);

        // cc.loader.loadRes('prefabs/Test', cc.Prefab, (err, res) => {
        //     let view = cc.instantiate(res)
            
        //     this.popupLayer.addChild(view)
        // })
    },

    // update (dt) {},
});
