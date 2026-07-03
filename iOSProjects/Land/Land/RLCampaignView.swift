//
//  RLCampaignView.swift
//  Land
//
//  Created by apple on 16/1/1.
//  Copyright © 2016年 G & B. All rights reserved.
//

import UIKit

class RLCampaignView : UIView {
    var delegate:RLCampaignViewDelegate!
    
    var targetInfor:TerritoryInfo! {
        didSet {
            self.targetNameLabel.text = self.targetInfor.name
            self.targetCountOfSoldierLabel.text = "\(self.targetInfor.armyQuantity)"
        }
    }
    
    @IBOutlet weak var targetNameLabel: UILabel!
    @IBOutlet weak var targetCountOfSoldierLabel: UILabel!
    @IBOutlet weak var countOfSoldierLabel: UILabel!
    @IBOutlet weak var countOfGoldLabel: UILabel!
    @IBOutlet weak var changeCountOfSoldierSlider: UISlider!
    
    fileprivate var countOfSoldier2Campaign:Int {
        get {
            return Int(self.changeCountOfSoldierSlider.value)
        }
    }
    
    func setMaxCountOfSoldier2Campaign(_ maxCount:Int) {
        self.changeCountOfSoldierSlider.maximumValue = Float(maxCount)
        self.changeCountOfSoldierSlider.value = Float(maxCount / 2)
        self.resetLabelView()
    }
    
    @IBAction func resetLabelView() {
        self.countOfSoldierLabel.text = "\(self.countOfSoldier2Campaign)"
        self.countOfGoldLabel.text = "\(PRICE_OF_EACH_SOLDIER_2_CAMPAIGN * self.countOfSoldier2Campaign)"
    }
    
    @IBAction func campaign() {
        self.delegate.campaignOnCampaignView(self.countOfSoldier2Campaign, targetInfor:self.targetInfor)
    }
    @IBAction func cancel() {
        self.delegate.cancelOnCampaignView()
    }
}

protocol RLCampaignViewDelegate {
    func campaignOnCampaignView(_ countOfSoldier2Campaign:Int, targetInfor:TerritoryInfo)
    func cancelOnCampaignView()
}
