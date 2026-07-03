//
//  DGMissions.swift
//  DiceGame
//
//  Created by apple on 15/8/6.
//  Copyright (c) 2015年 WhaleStudio. All rights reserved.
//

import Foundation



public let MISSION_DAILY_GAME_EVERYDAY = "missiondailygameeveryday"
public let MISSION_DAILY_GAME_IN_PRIVATE_ROOM = "missiondailygameinprivateroom"
public func MISSION_DESCRIPTION(_ typeOfMission:String) -> String? {
    switch typeOfMission {
    case MISSION_DAILY_GAME_EVERYDAY:
        return NSLocalizedString("A_Round_A_Day", comment:"")
    case MISSION_DAILY_GAME_IN_PRIVATE_ROOM:
        return NSLocalizedString("Invite_Friend_2_Private_Room_A_Day", comment:"")
    default:
        return nil
    }
}
