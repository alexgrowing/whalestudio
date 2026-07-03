//
//  RLTerritoryInforViewController.swift
//  Land
//
//  Created by apple on 15/12/29.
//  Copyright © 2015年 G & B. All rights reserved.
//

import UIKit

class RLTerritoryInforViewController : UIViewController {
    var delegate:RLTerritoryInforViewControllerDelegate!
    
    @IBOutlet weak var nameOfTerritoryLabel: UILabel!
    @IBOutlet weak var ownerOfTerritoryLabel: UILabel!
    @IBOutlet weak var latitudeLabel: UILabel!
    @IBOutlet weak var longitudeLabel: UILabel!
    @IBOutlet weak var levelOfTerritoryLabel: UILabel!
    @IBOutlet weak var countOfArmyLabel: UILabel!
    @IBOutlet weak var levelOfArmyLabel: UILabel!
    
    func setInfor(infor:TerritoryInfo) {
        self.nameOfTerritoryLabel.text = infor.name
        self.ownerOfTerritoryLabel.text = infor.ownerName.characters.count > 0 ? infor.ownerName : "无"
        self.latitudeLabel.text = "\(Float(infor.latitude100) / 100)"
        self.longitudeLabel.text = "\(Float(infor.longitude100) / 100)"
        self.levelOfTerritoryLabel.text = "\(infor.levelOfTerritory)"
        self.countOfArmyLabel.text = "\(infor.armyQuantity)"
        self.levelOfArmyLabel.text = "\(infor.armyLevel)"
    }
    
    @IBAction func attack() {
        if let theDelegate = self.delegate {
            theDelegate.attackOnTerritoryInforView()
        }
    }
    
    @IBAction func back() {
        if let theDelegate = self.delegate {
            theDelegate.backOnTerritoryInforView()
        }
    }
}

protocol RLTerritoryInforViewControllerDelegate {
    func backOnTerritoryInforView()
    func attackOnTerritoryInforView()
}
