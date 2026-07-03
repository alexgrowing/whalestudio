//
//  DGRingGameViewController.swift
//  DiceGame
//
//  Created by apple on 15/8/8.
//  Copyright (c) 2015年 WhaleStudio. All rights reserved.
//

import UIKit
import DiceGameLib

class DGRingGameViewController : DGInternetGameViewController {
    fileprivate var amIAttacker = true
    
    /*
    override func addSubviews2Waiting4OpponentIntoRoomView(waiting4OpponentView:UIView) {
        let sizeOfFrame = waiting4OpponentView.bounds.size
        
        self.waiting4OpponentInfoLabel = DGUIUtils.createMiddleUILabel(CGRectMake(0,sizeOfFrame.height/2 - DGFonts.MIDDLE_FONT_SIZE * 2,sizeOfFrame.width, DGFonts.MIDDLE_FONT_SIZE), initString: "等待挑战者攻擂")
        waiting4OpponentView.addSubview(self.waiting4OpponentInfoLabel)
    }
 */
    /*
    override func addPlayer2Room(player: DGPlayer) {
        super.addPlayer2Room(player)
        
        if self.isRoomFull() {
            self.waiting4OpponentInfoLabel.text = "准备开始战斗"
        } else {
            self.waiting4OpponentInfoLabel.text = "等待挑战者攻擂"
        }
    }
    */
    /*
    override func beNotifiedOfMyRoomID(roomID: String, myCards: [String : Int], countOfFullPlayers: Int, playersAlreadyInRoom: [DGPlayer]) {
        super.beNotifiedOfMyRoomID(roomID, myCards: myCards, countOfFullPlayers: countOfFullPlayers, playersAlreadyInRoom: playersAlreadyInRoom)
        
        self.amIAttacker = true
    }
    */
    
    override func addSubviews2MatchingPlayerView(_ matchingPlayerView: UIView) {
        super.addSubviews2MatchingPlayerView(matchingPlayerView)
        
        self.setTextOfMatchingPlayerInforLabel(NSLocalizedString("Finding_Arena", comment:""))
    }
    
    override func textOfNewRoundButtonOnIWinRound() -> String {
        return NSLocalizedString("New_Challenge", comment:"")
    }
    
    override func textOfNewRoundButtonOnINotWinRound() -> String {
        return NSLocalizedString("New_Arena", comment:"")
    }
    
    override func textOfNewRoundButtonOnSomeoneLeft() -> String {
        return NSLocalizedString("New_Challenge", comment:"")
    }
    
    /*
    override func action4StartNewRoundOnIWinRound() {
        self.clearOtherPlayers()
        
        self.waiting4OpponentInfoLabel.text = "等待挑战者攻擂"
        self.currentCardOfView = .Waiting4OpponentIntoRoom
        self.client.notifyServerIAmReady4NewRound()
        self.amIAttacker = false
    }
    
    override func action4StartNewRoundOnINotWinRound() {        
        self.clearOtherPlayers()
        self.client.notifyServerOfRing()
        self.amIAttacker = true
    }
     */
    
    override func action4StartNewRoundOnIWinRound() {
        self.setTextOfMatchingPlayerInforLabel(NSLocalizedString("Waiting_4_New_Challenger", comment:""))
        self.currentCardOfView = .waitingNewChallenger
        
        self.client.notifyServerIAmReady4NewRound()
    }
    
    override func action4StartNewRoundOnINotWinRound() {
        self.setTextOfMatchingPlayerInforLabel(NSLocalizedString("Finding_Arena", comment:""))
        self.currentCardOfView = .matchingPlayer

        self.client.notifyServerOfRing()
    }

    override func action4StartNewRoundOnSomeoneLeft() {
        self.setTextOfMatchingPlayerInforLabel(NSLocalizedString("Waiting_4_New_Challenger", comment:""))
        self.currentCardOfView = .matchingPlayer

        self.client.notifyServerOfRing()
    }
 
}
