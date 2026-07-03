//
//  RLMyFightsView.swift
//  Land
//
//  Created by apple on 16/2/17.
//  Copyright © 2016年 G & B. All rights reserved.
//

import UIKit

class RLMyFightsView : UIView, UITableViewDataSource, UITableViewDelegate {
    var delegate:RLMyFightsViewDelegate!
    
    @IBOutlet weak var typeOfFightsInfoControl: UISegmentedControl!
    @IBOutlet weak var fightsInfoTableView: UITableView!
    
    var allMyFights:(asAttacker:[FightResultInfo], asDefender:[FightResultInfo]) = ([FightResultInfo](), [FightResultInfo]()) {
        didSet {
            self.allMyFights.asAttacker.sort { (info1, info2) -> Bool in
                return info1.occured.compare(info2.occured as Date) == .orderedDescending
            }
            self.allMyFights.asDefender.sort { (info1, info2) -> Bool in
                return info1.occured.compare(info2.occured as Date) == .orderedDescending
            }
            self.fightsInfoTableView.reloadData()
        }
    }
    
    func prepareFightsInfoTableView() {
        self.fightsInfoTableView.dataSource = self
        self.fightsInfoTableView.delegate = self
    }
    
    // MARK: - UITableViewDataSource
    func numberOfSections(in tableView: UITableView) -> Int {
        return 1
    }
    
    func tableView(_ tableView: UITableView, numberOfRowsInSection section: Int) -> Int {
        return self.fightsInTableView().count
    }
    
    func tableView(_ tableView: UITableView, cellForRowAt indexPath: IndexPath) -> UITableViewCell {
        let cellIdentifier = "Cell"
        
        var cell = tableView.dequeueReusableCell(withIdentifier: cellIdentifier) as? TableCell4Fights
        if cell == nil {
            cell = TableCell4Fights(style: UITableViewCell.CellStyle.default, reuseIdentifier: cellIdentifier)
            cell?.selectionStyle = UITableViewCell.SelectionStyle.blue
            cell?.backgroundColor = UIColor.clear
            
            let widthOfCell = tableView.bounds.width
            
            cell?.occuredLabel = UILabel(frame:CGRect(x: 0,y: 0,width: widthOfCell,height: 10))
            cell?.addSubview((cell?.occuredLabel)!)
            cell?.occuredLabel.font = UIFont.systemFont(ofSize: 8)
            
            cell?.attackerLabel = UILabel(frame:CGRect(x: 0,y: 10,width: widthOfCell/2-20,height: cell!.bounds.height-10))
            cell?.addSubview((cell?.attackerLabel)!)
            cell?.attackerLabel.textAlignment = .right
            cell?.attackerLabel.font = UIFont.systemFont(ofSize: 12)
            
            let vsLabel = UILabel(frame:CGRect(x: widthOfCell/2-20,y: 10,width: 40,height: cell!.bounds.height-10))
            cell?.addSubview(vsLabel)
            vsLabel.text = "⚔"
            vsLabel.textAlignment = .center
            
            cell?.defenderLabel = UILabel(frame:CGRect(x: widthOfCell/2+20,y: 10,width: widthOfCell/2-20,height: cell!.bounds.height-10))
            cell?.addSubview((cell?.defenderLabel)!)
            cell?.defenderLabel.textAlignment = .left
            cell?.defenderLabel.font = UIFont.systemFont(ofSize: 12)
        }
        
        let fight = self.fightsInTableView()[(indexPath as NSIndexPath).row]
        
        let formatter = DateFormatter()
        formatter.dateFormat = "yyyy-MM-dd HH:mm:ss"
        cell?.occuredLabel.text = formatter.string(from: fight.occured as Date)
        cell?.attackerLabel.text = (fight.attackerWins ? "🚩" : "🏳") + fight.nameOfAttacker
        cell?.defenderLabel.text = (fight.attackerWins ? "🏳" : "🚩") + fight.nameOfDefender
        
        return cell!
    }
    
    // MARK: - UITableViewDelegate
    func tableView(_ tableView: UITableView, heightForRowAt indexPath: IndexPath) -> CGFloat {
        return 40
    }
    
    func tableView(_ tableView: UITableView, didSelectRowAt indexPath: IndexPath) {
        let selectedFight = self.fightsInTableView()[(indexPath as NSIndexPath).row]
        
        self.delegate.iKnowOnMyFightsView()
        self.delegate.gotoLocationOnMyFightsView(selectedFight.latitude100, longitude100: selectedFight.longitude100)
    }
    
    // MARK: - PrivateMethods
    fileprivate func fightsInTableView() -> [FightResultInfo] {
        if self.typeOfFightsInfoControl.selectedSegmentIndex == 0 {
            return self.allMyFights.asAttacker
        } else {
            return self.allMyFights.asDefender
        }
    }
    
    @IBAction func changeTypeOfFightsInfo() {
        self.fightsInfoTableView.reloadData()
    }
    
    @IBAction func iKnow() {
        self.delegate.iKnowOnMyFightsView()
    }
}

protocol RLMyFightsViewDelegate {
    func iKnowOnMyFightsView()
    
    func gotoLocationOnMyFightsView(_ latitude100:Int, longitude100:Int)
}

private class TableCell4Fights : UITableViewCell {
    var attackerLabel:UILabel!
    var defenderLabel:UILabel!
    var occuredLabel:UILabel!
    
    override init(style: UITableViewCell.CellStyle, reuseIdentifier: String?) {
        super.init(style:style, reuseIdentifier:reuseIdentifier)
    }

    required init?(coder aDecoder: NSCoder) {
        fatalError("init(coder:) has not been implemented")
    }
}
