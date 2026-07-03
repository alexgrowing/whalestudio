//
//  RLAddDiamondView.swift
//  Land
//
//  Created by apple on 15/12/31.
//  Copyright © 2015年 G & B. All rights reserved.
//

import UIKit

class RLAddDiamondView : UIView {
    var delegate:RLAddDiamondViewDelegate!
    
    @IBAction func buy() {
        self.delegate.buyOnAddDiamond()
    }
    @IBAction func cancel() {
        self.delegate.cancelOnAddDiamond()
    }
}

protocol RLAddDiamondViewDelegate {
    func buyOnAddDiamond()
    func cancelOnAddDiamond()
}
