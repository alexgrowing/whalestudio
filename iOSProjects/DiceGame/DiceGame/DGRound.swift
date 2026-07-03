//
//  DGRoundGameViewController.swift
//  DiceGame
//
//  Created by apple on 15/8/9.
//  Copyright (c) 2015年 WhaleStudio. All rights reserved.
//

import UIKit
import DiceGameLib

class DGRoundGameViewController : DGInternetGameViewController {
    /*
    private var roomIDLabel: UILabel!
    
    private var roomIDIAmIN:String! {
        didSet {
            self.roomIDLabel.text = "房间号:\(self.roomIDIAmIN)"
        }
    }
    
    override func addSubviews2Waiting4OpponentIntoRoomView(waiting4OpponentView:UIView) {
        let sizeOfParentView = waiting4OpponentView.frame.size
        let centerYOfParentView = sizeOfParentView.height/2
        
        let distance2CenterY:CGFloat = 40
        
        self.roomIDLabel = DGUIUtils.createMiddleUILabel(CGRectMake(0,centerYOfParentView-distance2CenterY-DGFonts.MIDDLE_FONT_SIZE, sizeOfParentView.width, DGFonts.MIDDLE_FONT_SIZE), initString: "")
        waiting4OpponentView.addSubview(self.roomIDLabel)
        
        let wechatInviteFriendButton = DGUIUtils.createUIButton(CGRectMake(0,centerYOfParentView+distance2CenterY,sizeOfParentView.width, DGFonts.NORMAL_FONT_SIZE), titleOfButton: "邀请微信好友对战", target: self, action: #selector(DGRoundGameViewController.inviteWeixinFriend2Room))
        waiting4OpponentView.addSubview(wechatInviteFriendButton)
        
        /*
        let qqInviteFriendButton = DGUIUtils.createUIButton(CGRectMake(0,centerYOfParentView+distance2CenterY*3,sizeOfParentView.width, DGFonts.NORMAL_FONT_SIZE), titleOfButton: "邀请QQ好友对战", target: self, action: Selector("inviteQQFriend2Room"))
        waiting4OpponentView.addSubview(qqInviteFriendButton)
*/
    }
    
    override func beNotifiedOfMyRoomID(roomID:String, myCards:[String:Int], countOfFullPlayers:Int, playersAlreadyInRoom:[DGPlayer]/*self included*/) {
        super.beNotifiedOfMyRoomID(roomID, myCards:myCards, countOfFullPlayers:countOfFullPlayers, playersAlreadyInRoom: playersAlreadyInRoom)
        
        self.roomIDIAmIN = roomID
    }
    
    // MARK: - Instance Method
    func inviteWeixinFriend2Room() {
        if let myRoomID = self.roomIDIAmIN {
            let req = SendMessageToWXReq()
            req.scene = Int32(WXSceneSession.rawValue) // WXSceneTimeline.value表示发到朋友圈
            
            req.bText = false
            req.message = WXMediaMessage()
            req.message.title = "挑战书"
            req.message.description = "谁敢与我一战"
            req.message.setThumbImage(UIImage(named:DGBundle.LOGO)!)
            
            let ext = WXWebpageObject()
            ext.webpageUrl = "\(SERVER_CHALLENGE_URL)?\(myRoomID)"
            req.message.mediaObject = ext;
            
            WXApi.sendReq(req)
        }
    }
 */
}
