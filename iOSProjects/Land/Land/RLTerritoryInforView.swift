//
//  RLTerritoryInforView.swift
//  Land
//
//  Created by apple on 15/12/30.
//  Copyright © 2015年 G & B. All rights reserved.
//

import UIKit

class RLTerritoryInforView : UIView {
    var delegate:RLTerritoryInforViewDelegate!
    var infor:TerritoryInfo! {
        didSet {
            self.nameOfTerritoryLabel.text = self.infor.name
            self.ownerLabel.text = self.infor.ownerName.count > 0 ? self.infor.ownerName : "无"
            self.latitudeLabel.text = "\(Float(self.infor.latitude100) / 100)"
            self.longitudeLabel.text = "\(Float(self.infor.longitude100) / 100)"
            self.levelOfTerritoryLabel.text = "\(self.infor.levelOfTerritory)"
            self.countOfArmyLabel.text = "\(self.infor.armyQuantity)"
            self.levelOfArmyLabel.text = "\(self.infor.armyLevel)"
            
            if let theUser = RLUser.getCurrentUser() , theUser.uuid == infor.ownerUUID {
                self.doAttack = false
            } else {
                self.doAttack = true
            }
        }
    }
    
    fileprivate var doAttack:Bool = true {
        didSet {
            if self.doAttack {
                self.attackOrConfigureButton.setTitle("⚔进攻", for: .normal)
            } else {
                self.attackOrConfigureButton.setTitle("🏢管理", for: .normal)
            }
        }
    }
    
    @IBOutlet weak var nameOfTerritoryLabel: UILabel!
    @IBOutlet weak var latitudeLabel: UILabel!
    @IBOutlet weak var longitudeLabel: UILabel!
    @IBOutlet weak var ownerLabel: UILabel!
    @IBOutlet weak var levelOfTerritoryLabel: UILabel!
    @IBOutlet weak var countOfArmyLabel: UILabel!
    @IBOutlet weak var levelOfArmyLabel: UILabel!
    @IBOutlet weak var attackOrConfigureButton: UIButton!
    
    @IBAction func attack() {
        if self.doAttack {
            self.delegate.attackOnTerritoryInforView(self.infor)
        } else {
            self.delegate.configureOnTerritoryInforView(self.infor)
        }
    }
    @IBAction func back() {
        self.delegate.backOnTerritoryInforView()
    }
}

protocol RLTerritoryInforViewDelegate {
    func backOnTerritoryInforView()
    func attackOnTerritoryInforView(_ target:TerritoryInfo)
    func configureOnTerritoryInforView(_ target:TerritoryInfo)
}
