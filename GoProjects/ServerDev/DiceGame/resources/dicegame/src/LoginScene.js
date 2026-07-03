(function(ns) {
    var LoginScene = ns.LoginScene = Hilo.Class.create({
        Extends : Hilo.Container,
        constructor:function(properties) {
            LoginScene.superclass.constructor.call(this, properties);
            this.init(properties)
        },

        cancelButton:null,

        init:function (properties) {
            var text = new Hilo.Text({
                text:"正在登录",
                font:"60px 宋体",
                color:"#FFFFFF",
                textAlign:"center",
                maxWidth:this.width,
                width:this.width,
                x:0,
                y:this.height / 2
            }).addTo(this);
        }
    })
})(window.game);