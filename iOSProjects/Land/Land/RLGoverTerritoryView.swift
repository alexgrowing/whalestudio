//
//  RLGoverTerritoryView.swift
//  Land
//
//  Created by apple on 16/1/1.
//  Copyright © 2016年 G & B. All rights reserved.
//

import UIKit

class RLGoverTerritoryView : UIView {
    var delegate:RLGoverTerritoryViewDelegate!
    
    @IBOutlet weak var nameOfTerritoryField: UITextField!
    @IBOutlet weak var countOfSoldier2Defend: UILabel!
    @IBOutlet weak var countOfSoldier2DefendSlider: UISlider!
    @IBOutlet weak var okButton: UIButton!
    @IBOutlet weak var bottomConstant: NSLayoutConstraint!
    
    var maxCountOfSoldier:Int! {
        didSet {
            self.countOfSoldier2DefendSlider.maximumValue = Float(self.maxCountOfSoldier)
            
            self.resetViewLabels()
        }
    }
    var originalInfor:TerritoryInfo! {
        didSet {
            self.nameOfTerritoryField.text = self.originalInfor.name
            self.countOfSoldier2DefendSlider.value = Float(self.originalInfor.armyQuantity)
            
            self.resetViewLabels()
        }
    }

    @IBAction func resetViewLabels() {
        self.countOfSoldier2Defend.text = "\(Int(self.countOfSoldier2DefendSlider.value))"
        
        var enableOkButton = false
        if let nameOfTerritory = self.nameOfTerritoryField.text , nameOfTerritory.count > 0 {
            enableOkButton = true
        }
        
        self.okButton.isEnabled = enableOkButton
    }
    
    @IBAction func ok() {
        UIResponder.resignFirstResponder()
        
        self.delegate.okOnGoverTerritoryView(self.originalInfor, newName:self.nameOfTerritoryField.text!, newCountOfSoldier: Int(self.countOfSoldier2DefendSlider.value))
    }
    @IBAction func cancel() {
        UIResponder.resignFirstResponder()

        self.delegate.cancelOnGoverTerritoryView()
    }
    
    // MARK: - Instance Methods
    func onKeyboardWillShow(heightOfKeyobard:CGFloat) {
        self.bottomConstant.constant = heightOfKeyobard
    }
    
    func onKeyboardWillHide() {
        self.bottomConstant.constant = 0
    }
}

protocol RLGoverTerritoryViewDelegate {
    func okOnGoverTerritoryView(_ oldInfor:TerritoryInfo, newName:String, newCountOfSoldier:Int)
    func cancelOnGoverTerritoryView()
}
