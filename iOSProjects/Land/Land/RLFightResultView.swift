//
//  RLFightResultView.swift
//  Land
//
//  Created by apple on 16/1/1.
//  Copyright © 2016年 G & B. All rights reserved.
//

import UIKit

class RLFightResultView : UIView {
    var delegate:RLFightResultViewDelegate!
    
    @IBOutlet weak var resultLabel: UILabel!
    @IBOutlet weak var goldCostLabel: UILabel!
    @IBOutlet weak var myDeadLabel: UILabel!
    @IBOutlet weak var opponentDeadLabel: UILabel!
    @IBOutlet weak var typeOfCaptiveLabel: UILabel!
    @IBOutlet weak var countOfCaptiveLabel: UILabel!
    
    var fightResult:FightResultInfo! {
        didSet {
            if self.fightResult.attackerWins {
                self.resultLabel.text = "胜"
                self.resultLabel.textColor = UIColor.red
                self.typeOfCaptiveLabel.text = "俘虏"
            } else {
                self.resultLabel.text = "败"
                self.resultLabel.textColor = UIColor.green
                self.typeOfCaptiveLabel.text = "被俘虏"
            }
            
            self.goldCostLabel.text = "\(self.fightResult.goldCost)"
            self.myDeadLabel.text = "\(self.fightResult.deathOfAttacker)"
            self.opponentDeadLabel.text = "\(self.fightResult.deathOfDefender)"
            self.countOfCaptiveLabel.text = "\(self.fightResult.captive)"
        }
    }
    
    @IBAction func ok() {
        self.delegate.okOnFightResultView()
    }
}

protocol RLFightResultViewDelegate {
    func okOnFightResultView()
}
