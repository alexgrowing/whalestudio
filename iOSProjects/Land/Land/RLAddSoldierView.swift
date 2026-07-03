//
//  RLAddArmyView.swift
//  Land
//
//  Created by apple on 15/12/30.
//  Copyright © 2015年 G & B. All rights reserved.
//

import UIKit

class RLAddSoldierView : UIView {
    var delegate:RLAddSoldierViewDelegate!

    @IBOutlet weak var countOfSoldier2RecruitSlider: UISlider!
    @IBOutlet weak var countOfSoldierRecruitLabel: UILabel!
    @IBOutlet weak var countOfGoldCostLabel: UILabel!
    @IBOutlet weak var timeCostLabel: UILabel!
    
    fileprivate var countOfSoldier2Recruit:Int {
        get {
            return Int(self.countOfSoldier2RecruitSlider.value)
        }
    }
    
    func setMaxCountOfRecruit(_ maxCount:Int) {
        self.countOfSoldier2RecruitSlider.maximumValue = Float(maxCount)
        self.countOfSoldier2RecruitSlider.value = Float(maxCount / 2)
        self.resetLabelView()
    }
    
    @IBAction func resetLabelView() {
        self.countOfSoldierRecruitLabel.text = "\(self.countOfSoldier2Recruit)"
        self.countOfGoldCostLabel.text = "\(PRICE_OF_EACH_SOLDIOR_2_RECRUIT * self.countOfSoldier2Recruit)"
        
        var countOfTeams = self.countOfSoldier2Recruit / COUNT_OF_SOLDIER_TRAINING_PER_MINUTE
        if self.countOfSoldier2Recruit % COUNT_OF_SOLDIER_TRAINING_PER_MINUTE > 0 {
            countOfTeams = countOfTeams + 1
        }

        self.timeCostLabel.text = "\(countOfTeams)分"
    }
    @IBAction func recruit() {
        self.delegate.recruitOnAddSoldierView(self.countOfSoldier2Recruit)
    }
    @IBAction func back() {
        self.delegate.backOnAddSoldierView()
    }
}

protocol RLAddSoldierViewDelegate {
    func recruitOnAddSoldierView(_ countOfArmyRecruit:Int)
    func backOnAddSoldierView()
}
