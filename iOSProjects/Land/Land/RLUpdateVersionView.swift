//
//  RLUpdateVersionView.swift
//  Land
//
//  Created by apple on 16/1/18.
//  Copyright © 2016年 G & B. All rights reserved.
//

import UIKit

class RLUpdateVersionView : UIView {
    var delegate:RLUpdateVersionViewDelegate!
    
    @IBAction func updateVersion() {
        self.delegate.onUpdateVersion()
    }
}

protocol RLUpdateVersionViewDelegate {
    func onUpdateVersion()
}
