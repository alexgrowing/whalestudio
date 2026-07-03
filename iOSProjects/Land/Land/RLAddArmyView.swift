//
//  RLAddArmyView.swift
//  Land
//
//  Created by apple on 15/12/30.
//  Copyright © 2015年 G & B. All rights reserved.
//

import UIKit

class RLAddArmyView : UIView {
    var delegate:RLAddArmyViewDelegate!

    @IBOutlet weak var countOfArmy2RecruitSlider: UISlider!
    @IBOutlet weak var countOfArmyRecruitLabel: UILabel!
    @IBOutlet weak var countOfGoldCostLabel: UILabel!
    
    private var countOfArmy2Recruit:Int {
        get {
            return Int(self.countOfArmy2RecruitSlider.value)
        }
    }
    
    func setMaxCountOfRecruit(maxCount:Int) {
        self.countOfArmy2RecruitSlider.maximumValue = Float(maxCount)
        self.countOfArmy2RecruitSlider.value = Float(maxCount / 2)
        self.resetLabelView()
    }
    
    @IBAction func resetLabelView() {
        self.countOfArmyRecruitLabel.text = "\(self.countOfArmy2Recruit)"
        self.countOfGoldCostLabel.text = "\(PRICE_OF_EACH_SOLDIOR_2_RECRUIT * self.countOfArmy2Recruit)"
    }
    @IBAction func recruit() {
        self.delegate.recruitOnAddArmyView(self.countOfArmy2Recruit)
    }
    @IBAction func back() {
        self.delegate.backOnAddArmyView()
    }
}

protocol RLAddArmyViewDelegate {
    func recruitOnAddArmyView(countOfArmyRecruit:Int)
    func backOnAddArmyView()
}