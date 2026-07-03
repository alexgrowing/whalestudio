//
//  DGPrivate.swift
//  DiceGame
//
//  Created by apple on 16/6/6.
//  Copyright © 2016年 WhaleStudio. All rights reserved.
//

import DiceGameLib

class DGPrivateGameViewController : DGRoundGameViewController {
    fileprivate var roomIDIAmIN:String! {
        didSet {
            self.inviteLabel.isHidden = false
            self.inviteLabel.text = "\(NSLocalizedString("Invite_Friend_2_This_Room", comment:""))：\(self.roomIDIAmIN!)"
        }
    }
    fileprivate var inviteLabel:UILabel!
    
    override func beNotifiedOfMyRoomID(_ roomID: String) {
        super.beNotifiedOfMyRoomID(roomID)
        
        self.roomIDIAmIN = roomID
    }
    
    override func beNotified2StartRound(_ roundIndex: Int, myCards: [String : Int], playersInRoom: [DGPlayer]) {
        super.beNotified2StartRound(roundIndex, myCards: myCards, playersInRoom: playersInRoom)
        
        self.inviteLabel.isHidden = true
    }
    
    override func addSubviews2MatchingPlayerView(_ matchingPlayerView: UIView) {
        super.addSubviews2MatchingPlayerView(matchingPlayerView)
                
        self.inviteLabel = DGUIUtils.createUILabel(initString: "")
        matchingPlayerView.addSubview(self.inviteLabel)
        self.inviteLabel.snp.makeConstraints { (make) in
            make.center.equalTo(matchingPlayerView)
            make.left.equalTo(0)
            make.right.equalTo(0)
            make.height.equalTo(DGFonts.SMALL_FONT_SIZE)
        }
        self.inviteLabel.isHidden = true
    }
    
    override func textOfNewRoundButtonOnSomeoneLeft() -> String {
        return NSLocalizedString("Create_Private_Room", comment:"")
    }
    
    override func action4StartNewRoundOnSomeoneLeft() {
        self.currentCardOfView = .matchingPlayer

        self.client.notifyServerOfCreateANewRoom()
    }
    
    // MARK: - Instance Method
//    func inviteWeixinFriend2Room() {
//        if let myRoomID = self.roomIDIAmIN {
//            let req = SendMessageToWXReq()
//            req.scene = Int32(WXSceneSession.rawValue) // WXSceneTimeline.value表示发到朋友圈
//            
//            req.bText = false
//            req.message = WXMediaMessage()
//            req.message.title = NSLocalizedString("Challenge", comment:"")
//            req.message.description = NSLocalizedString("Who_Can_Beat_Me", comment:"")
//            req.message.setThumbImage(UIImage(named:DGBundle.LOGO)!)
//            
//            let ext = WXWebpageObject()
//            ext.webpageUrl = "\(SERVER_CHALLENGE_URL)?\(myRoomID)"
//            req.message.mediaObject = ext;
//            
//            WXApi.send(req)
//        }
//    }
    
    
    /*
     func inviteQQFriend2Room() {
     if let myRoomID = self.roomIDIAmIN where !self.isRoomFull() {
     if let newsObj = QQApiNewsObject.objectWithURL(NSURL(string: "\(DGInternetMessageSenderReceiver.SERVER_CHALLENGE_URL)?\(myRoomID)"), title: "挑战书", description: "谁敢与我一战", previewImageData:UIImageJPEGRepresentation(UIImage(named:DGBundle.LOGO)!, 1.0)) as? QQApiObject {
     
     let req = SendMessageToQQReq(content: newsObj)
     QQApiInterface.sendReq(req)
     }
     }
     }
     */
}
