//
//  WLGame.swift
//  WhaleLib
//
//  Created by apple on 16/2/26.
//  Copyright © 2016年 WhaleStudio. All rights reserved.
//

import Foundation
import GameKit

public func getUUIDFromLocalPlayer(_ localPlayer:GKLocalPlayer) -> String? {
    return localPlayer.playerID.replacingOccurrences(of: ":", with: "", options: NSString.CompareOptions.literal, range: nil)
}
