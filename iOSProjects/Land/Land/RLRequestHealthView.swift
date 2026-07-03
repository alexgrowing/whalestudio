//
//  RLRequestHealthView.swift
//  Land
//
//  Created by apple on 16/1/21.
//  Copyright © 2016年 G & B. All rights reserved.
//

import UIKit

class RLRequestHealthView : UIView {
    var delegate:RLRequestHealthViewDelegate!
    
    @IBAction func activate() {
        self.delegate.activateOnRequestHealthView()
    }
}

protocol RLRequestHealthViewDelegate {
    func activateOnRequestHealthView()
}