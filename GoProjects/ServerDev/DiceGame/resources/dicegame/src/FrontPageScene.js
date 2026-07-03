(function (ns) {
    var FrontPageScene = ns.FrontPageScene = Hilo.Class.create({
        Extends : ns.Scene,
        constructor:function (properties) {
            FrontPageScene.superclass.constructor.call(this, properties);
            this.init(properties)
        },

        quickstartButton:null,
        arenaButton:null,
        createprivateButton:null,
        intoprivateButton:null,
        rankButton:null,
        informationButton:null,

        init:function (properties) {
            // var widthOfButton = this.width/15*4;
            // var heightOfButton = widthOfButton/3*2;
            // var paddingBetweenButtons = this.width/90*7;

            var widthOfButton = this.width/3;
            var heightOfButton = widthOfButton/3*2;
            var paddingBetweenButtons = this.width/18;

            var widthOfButtonView = widthOfButton * 2 + paddingBetweenButtons;
            var heightOfButtonView = heightOfButton * 3 + paddingBetweenButtons * 2;

            var buttonContainer = new Hilo.Container({
                width:widthOfButtonView,
                height:heightOfButtonView,
                x:(this.width - widthOfButtonView) / 2,
                y:(this.height - heightOfButtonView) /2
            }).addTo(this);

            this.quickstartButton = this.asset.createBigButton({
                text:"快速开始",color:"black",wsTextHeight:heightOfButton/6,
                x:0,y:0,
                width:widthOfButton,height:heightOfButton
            }).addTo(buttonContainer);
            this.arenaButton = this.asset.createBigButton({
                text : "擂台赛",color:"black",wsTextHeight:heightOfButton/6,
                x:buttonContainer.width - widthOfButton,y: 0,
                width:widthOfButton,height:heightOfButton
            }).addTo(buttonContainer);
            this.createprivateButton = this.asset.createBigButton({
                text :"创建私密房间",color:"black",wsTextHeight:heightOfButton/6,
                x:0, y:heightOfButton + paddingBetweenButtons,
                width:widthOfButton,height:heightOfButton
            }).addTo(buttonContainer);
            this.intoprivateButton = this.asset.createBigButton({
                text : "进入私密房间",color:"black",wsTextHeight:heightOfButton/6,
                x:buttonContainer.width - widthOfButton, y:heightOfButton + paddingBetweenButtons,
                width:widthOfButton,height:heightOfButton
            }).addTo(buttonContainer);
            this.rankButton = this.asset.createBigButton({
                text : "排名",color:"black",wsTextHeight:heightOfButton/6,
                x:0, y:buttonContainer.height - heightOfButton,
                width:widthOfButton,height:heightOfButton
            }).addTo(buttonContainer);
            this.informationButton = this.asset.createBigButton({
                text : "信息",color:"black",wsTextHeight:heightOfButton/6,
                x:buttonContainer.width - widthOfButton, y:buttonContainer.height - heightOfButton,
                width:widthOfButton,height:heightOfButton
            }).addTo(buttonContainer);
        }
    })
})(window.game);