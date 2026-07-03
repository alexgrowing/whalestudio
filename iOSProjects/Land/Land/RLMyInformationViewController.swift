//
//  RLMyInformationViewController.swift
//  Land
//
//  Created by alex on 2018/10/13.
//  Copyright © 2018年 G & B. All rights reserved.
//

import UIKit
import WhaleLib

class RLMyInformationViewController : UIViewController, UITableViewDataSource, UITableViewDelegate {
    private var informationTableView:UITableView!
    var delegate:RLMyInformationViewControllerDelegate!
    
    override func viewDidLoad() {
        let contentView = UIView()
        self.view.addSubview(contentView)
        contentView.snp.makeConstraints { (make) in
            make.edges.equalTo(self.view.safeAreaLayoutGuide.snp.edges)
        }
        
        let aboveTitleLabel = WLUI.createUILabel(text: "我")
        contentView.addSubview(aboveTitleLabel)
        aboveTitleLabel.snp.makeConstraints { (make) in
            make.height.equalTo(HEIGHT_OF_NAVIGATION_BAR)
            make.left.equalTo(0)
            make.right.equalTo(0)
            make.top.equalTo(0)
        }
        aboveTitleLabel.backgroundColor = UIColor.lightGray
        
        let backButton = WLUI.createUIButton(titleOfButton: "OK", target: self, action: #selector(RLMyInformationViewController.back))
        contentView.addSubview(backButton)
        backButton.backgroundColor = UIColor.lightGray
        backButton.snp.makeConstraints { (make) in
            make.height.equalTo(HEIGHT_OF_NAVIGATION_BAR)
            make.left.equalTo(0)
            make.right.equalTo(0)
            make.bottom.equalTo(0)
        }
        
        self.informationTableView = UITableView()
        contentView.addSubview(self.informationTableView)
        self.informationTableView.snp.makeConstraints { (make) in
            make.left.equalTo(0)
            make.right.equalTo(0)
            make.top.equalTo(aboveTitleLabel.snp.bottom)
            make.bottom.equalTo(backButton.snp.top)
        }
        self.informationTableView.tableFooterView = UIView(frame: CGRect.zero)
        self.informationTableView.dataSource = self
        self.informationTableView.delegate = self
        
        super.viewDidLoad()
    }
    
    func numberOfSections(in tableView: UITableView) -> Int {
        return 3
    }
    
    func tableView(_ tableView: UITableView, numberOfRowsInSection section: Int) -> Int {
        if section == 0 {
            return 1
        } else if section == 1 {
            return 3
        } else {
            return 5
        }
    }
    
    func tableView(_ tableView: UITableView, heightForRowAt indexPath: IndexPath) -> CGFloat {
        return 40
    }
    
    func tableView(_ tableView: UITableView, cellForRowAt indexPath: IndexPath) -> UITableViewCell {
        if indexPath.section == 2 && indexPath.row == 0 {
            return self.tableViewCell4WechatShare(tableView: tableView)
        }
        
        let currentCell:UITableViewCell
        if let cell = tableView.dequeueReusableCell(withIdentifier: INFORMATION_TABLE_CELL_VIEW_ID) {
            currentCell = cell
        } else {
            currentCell = UITableViewCell(style: .value1, reuseIdentifier: INFORMATION_TABLE_CELL_VIEW_ID)
            currentCell.selectionStyle = .none
        }
        
        guard let theUser = RLUser.getCurrentUser() else {return currentCell}
        
        if indexPath.section == 0 {
            currentCell.textLabel?.text = "昵称"
            currentCell.detailTextLabel?.text = theUser.name
            currentCell.accessoryType = .disclosureIndicator
        } else if indexPath.section == 1 {
            let nameText:String
            let valueText:String
            switch indexPath.row {
            case 0:
                nameText = "金币"
                valueText = "\(theUser.countOfGold)"
            case 1:
                nameText = "军队"
                valueText = "\(theUser.countOfSoldier)"
            default:
                nameText = "钻石"
                valueText = "\(theUser.countOfDiamond)"
            }
            
            currentCell.textLabel?.text = nameText
            currentCell.detailTextLabel?.text = valueText
        } else if indexPath.section == 2 {
            switch indexPath.row {
            case 1:
                currentCell.textLabel?.text = "我的足迹"
                currentCell.detailTextLabel?.text = "\(theUser.readOnlyFootprints.count)"
            case 2:
                currentCell.textLabel?.text = "相当于"
                RLClientActions.calculateSizeOfCountry(countOfLocations: theUser.readOnlyFootprints.count) { (square, partOfMatchedCountry, nameOfMatchedCountry) in
                    DispatchQueue.main.async {
                        currentCell.detailTextLabel?.text = String(format: "%.2f个%@", partOfMatchedCountry, nameOfMatchedCountry)
                    }
                }
            case 3:
                currentCell.textLabel?.text = "我的地盘"
                currentCell.detailTextLabel?.text = "\(theUser.readOnlyMyTerritories.count)"
            case 4:
                currentCell.textLabel?.text = "相当于"
                RLClientActions.calculateSizeOfCountry(countOfLocations: theUser.readOnlyMyTerritories.count) { (square, partOfMatchedCountry, nameOfMatchedCountry) in
                    DispatchQueue.main.async {
                        currentCell.detailTextLabel?.text = String(format: "%.2f个%@", partOfMatchedCountry, nameOfMatchedCountry)
                    }
                }
            default:
                // 当 case 0的时候
                currentCell.textLabel?.text = "成就"
                currentCell.detailTextLabel?.text = "微信分享"
            }
        }
        
        return currentCell
    }
    
    private func tableViewCell4WechatShare(tableView: UITableView) -> UITableViewCell {
        let currentCell:UITableViewCell
        if let cell = tableView.dequeueReusableCell(withIdentifier: INFORMATION_TABLE_CELL_VIEW_WECHAT_SHARE_ID) {
            currentCell = cell
        } else {
            currentCell = UITableViewCell(style: .value1, reuseIdentifier: INFORMATION_TABLE_CELL_VIEW_WECHAT_SHARE_ID)
            currentCell.textLabel?.text = "我的成就"
            let shareButton = UIButton()
            shareButton.setImage(UIImage(named: "share.png"), for: .normal)
            currentCell.addSubview(shareButton)
            shareButton.snp.makeConstraints { (make) in
                make.right.equalTo(-10)
                make.centerY.equalTo(currentCell.snp.centerY)
                make.height.equalTo(30)
                make.width.equalTo(30)
            }
            shareButton.addTarget(self, action: #selector(self.share2WechatFriend), for: .touchUpInside)
        }
        
        return currentCell
    }
    
    func tableView(_ tableView: UITableView, heightForFooterInSection section: Int) -> CGFloat {
        return 10
    }
    
    func tableView(_ tableView: UITableView, viewForFooterInSection section: Int) -> UIView? {
        let id4Reuse = "footview"
        var footView = tableView.dequeueReusableHeaderFooterView(withIdentifier: id4Reuse)
        if footView == nil {
            footView = UITableViewHeaderFooterView(reuseIdentifier: id4Reuse)
        }
        
        return footView
    }
    
    func tableView(_ tableView: UITableView, didSelectRowAt indexPath: IndexPath) {
        guard let theUser = RLUser.getCurrentUser() else {return}

        if indexPath.section == 0 && indexPath.row == 0 {
            // 点击了昵称
            let message:String
            let enoughDiamond:Bool
            if theUser.free2Rename {
                message = "免费"
                enoughDiamond = true
            } else {
                message = "消耗10颗钻石"
                enoughDiamond = theUser.countOfDiamond > 10
            }
            let confirmVC = UIAlertController(title: "设置名字", message: message, preferredStyle: .alert)
            confirmVC.addTextField { (tf) in
                tf.placeholder = "新名字"
                tf.text = theUser.name
            }
            if enoughDiamond {
                confirmVC.addAction(UIAlertAction(title: "确定", style: .default, handler: { (action) in
                    guard let theNewName = confirmVC.textFields?.first?.text else {return}
                    
                    if theNewName.count == 0 {
                        return
                    }
                    
                    RLClientActions.rename(theNewName, callback: { (errorCode:Int) -> Void in
                        if errorCode != ERROR_NONE {
                            return
                        }
                        DispatchQueue.main.async(execute: {
                            self.informationTableView.reloadData()
                        })
                    })
                }))
            } else {
                confirmVC.addAction(UIAlertAction(title: "钻石不足", style: .default, handler: { (action) in
                    
                }))
            }
            confirmVC.addAction(UIAlertAction(title: "取消", style: .cancel, handler: { (action) in
                // do nothing
            }))
            
            self.present(confirmVC, animated: true) {
                // do nothing
            }
        }
    }
    
    // MARK: - Instance Method
    @objc func back() {
        self.delegate.myInformationViewControllerWillDismiss()
        self.dismiss(animated: true, completion: nil)
    }
    
    @objc private func share2WechatFriend() {
        if let url = RLClientActions.createURL4Showoff() {
            let req = SendMessageToWXReq()
            req.scene = Int32(WXSceneSession.rawValue) // WXSceneTimeline.value表示发到朋友圈
            
            req.bText = false
            req.message = WXMediaMessage()
            req.message.title = "世界是我们的"
            req.message.description = "我的成就"
            req.message.setThumbImage(UIImage(named:"logo.png")!)
            
            let ext = WXWebpageObject()
            ext.webpageUrl = url
            req.message.mediaObject = ext;
            
            WXApi.send(req)
        }
    }
}

private let INFORMATION_TABLE_CELL_VIEW_ID = "INFORMATION_TABLE_CELL_VIEW_ID"
private let INFORMATION_TABLE_CELL_VIEW_WECHAT_SHARE_ID = "INFORMATION_TABLE_CELL_VIEW_WECHAT_SHARE_ID"

private let HEIGHT_OF_NAVIGATION_BAR:CGFloat = 40

protocol RLMyInformationViewControllerDelegate {
    func myInformationViewControllerWillDismiss()
}

/*
private let squares_of_all_countries:[CountryAndSquare] = [
    CountryAndSquare("俄罗斯",1707.5),
    CountryAndSquare("加拿大",997.1),
    CountryAndSquare("中国",960.1),
    CountryAndSquare("美国",936.4),
    CountryAndSquare("巴西",854.7),
    CountryAndSquare("澳大利亚",774.1),
    CountryAndSquare("印度",328.8),
    CountryAndSquare("阿根廷",278.0),
    CountryAndSquare("哈萨克斯坦",271.7),
    CountryAndSquare("苏丹",250.6),
    CountryAndSquare("阿尔及利亚",238.2),
    CountryAndSquare("刚果(金)",234.5),
    CountryAndSquare("沙特阿拉伯",215.0),
    CountryAndSquare("墨西哥",195.8),
    CountryAndSquare("印度尼西亚",190.5),
    CountryAndSquare("利比亚",176.0),
    CountryAndSquare("伊朗",163.3),
    CountryAndSquare("蒙古",156.7),
    CountryAndSquare("秘鲁",128.5),
    CountryAndSquare("乍得",128.4),
    CountryAndSquare("尼日尔",126.7),
    CountryAndSquare("安哥拉",124.7),
    CountryAndSquare("马里",124.0),
    CountryAndSquare("南非",122.1),
    CountryAndSquare("哥伦比亚",113.9),
    CountryAndSquare("埃塞俄比亚",110.4),
    CountryAndSquare("玻利维亚",109.9),
    CountryAndSquare("毛里塔尼亚",102.6),
    CountryAndSquare("埃及",100.1),
    CountryAndSquare("坦桑尼亚",94.5),
    CountryAndSquare("尼日利亚",92.4),
    CountryAndSquare("委内瑞拉",91.2),
    CountryAndSquare("纳米比亚",82.4),
    CountryAndSquare("莫桑比克",80.2),
    CountryAndSquare("巴基斯坦",79.6),
    CountryAndSquare("土耳其",77.5),
    CountryAndSquare("智利",75.7),
    CountryAndSquare("赞比亚",75.3),
    CountryAndSquare("缅甸",67.7),
    CountryAndSquare("阿富汗",65.2),
    CountryAndSquare("索马里",63.8),
    CountryAndSquare("中非",62.3),
    CountryAndSquare("乌克兰",60.4),
    CountryAndSquare("马达加斯加",58.7),
    CountryAndSquare("博茨瓦纳",58.2),
    CountryAndSquare("肯尼亚",58.0),
    CountryAndSquare("法国",55.2),
    CountryAndSquare("也门",52.8),
    CountryAndSquare("泰国",51.3),
    CountryAndSquare("西班牙",50.6),
    CountryAndSquare("土库曼斯坦",48.8),
    CountryAndSquare("喀唛隆",47.5),
    CountryAndSquare("巴布亚新几内亚",46.3),
    CountryAndSquare("瑞典",45.0),
    CountryAndSquare("乌兹别克斯坦",44.7),
    CountryAndSquare("摩洛哥",44.7),
    CountryAndSquare("伊拉克",43.8),
    CountryAndSquare("巴拉圭",40.7),
    CountryAndSquare("津巴布韦",39.1),
    CountryAndSquare("日本",37.8),
    CountryAndSquare("德国",35.7),
    CountryAndSquare("刚果（布）",34.2),
    CountryAndSquare("芬兰",33.8),
    CountryAndSquare("越南",33.2),
    CountryAndSquare("马来西亚",33.0),
    CountryAndSquare("挪威",32.4),
    CountryAndSquare("波兰",32.3),
    CountryAndSquare("科特迪瓦",32.2),
    CountryAndSquare("意大利",30.1),
    CountryAndSquare("菲律宾",30.0),
    CountryAndSquare("厄瓜多尔",28.4),
    CountryAndSquare("布基纳法索",27.4),
    CountryAndSquare("新西兰",27.1),
    CountryAndSquare("加蓬",26.8),
    CountryAndSquare("几内亚",24.6),
    CountryAndSquare("英国",24.5),
    CountryAndSquare("乌干达",24.1),
    CountryAndSquare("加纳",23.9),
    CountryAndSquare("罗马尼亚",23.8),
    CountryAndSquare("老挝",23.7),
    CountryAndSquare("圭亚那",21.5),
    CountryAndSquare("阿曼",21.2),
    CountryAndSquare("白俄罗斯",20.8),
    CountryAndSquare("吉尔吉斯",19.9),
    CountryAndSquare("塞内加尔",19.7),
    CountryAndSquare("叙利亚",18.5),
    CountryAndSquare("柬埔寨",18.1),
    CountryAndSquare("乌拉圭",17.7),
    CountryAndSquare("突尼斯",16.4),
    CountryAndSquare("苏里南",16.3),
    CountryAndSquare("尼泊尔",14.7),
    CountryAndSquare("孟加拉",14.4),
    CountryAndSquare("塔吉克斯坦",14.3),
    CountryAndSquare("希腊",13.2),
    CountryAndSquare("尼加拉瓜",13.0),
    CountryAndSquare("朝鲜",12.1),
    CountryAndSquare("马拉维",11.8),
    CountryAndSquare("贝宁",11.3),
    CountryAndSquare("洪都拉斯",11.2),
    CountryAndSquare("利比里亚",11.1),
    CountryAndSquare("古巴",11.1),
    CountryAndSquare("保加利亚",11.1),
    CountryAndSquare("危地马拉",10.9),
    CountryAndSquare("冰岛",10.3),
    CountryAndSquare("南斯拉夫",10.2),
    CountryAndSquare("韩国",9.9),
    CountryAndSquare("匈牙利",9.3),
    CountryAndSquare("葡萄牙",9.2),
    CountryAndSquare("约旦",8.9),
    CountryAndSquare("阿塞拜疆",8.7),
    CountryAndSquare("阿联酋",8.4),
    CountryAndSquare("奥地利",8.4),
    CountryAndSquare("捷克共和国",7.9),
    CountryAndSquare("巴拿马",7.6),
    CountryAndSquare("塞拉里昂",7.2),
    CountryAndSquare("爱尔兰",7.0),
    CountryAndSquare("格鲁吉亚",6.9),
    CountryAndSquare("斯里兰卡",6.6),
    CountryAndSquare("拉脱维亚",6.5),
    CountryAndSquare("立陶宛",6.5),
    CountryAndSquare("多哥",5.7),
    CountryAndSquare("克罗地亚",5.7),
    CountryAndSquare("哥斯达黎加",5.1),
    CountryAndSquare("斯洛伐克",4.9),
    CountryAndSquare("多米尼加",4.9),
    CountryAndSquare("不丹",4.7),
    CountryAndSquare("爱沙尼亚",4.5),
    CountryAndSquare("丹麦",4.3),
    CountryAndSquare("荷兰",4.1),
    CountryAndSquare("瑞士",4.1),
    CountryAndSquare("几内亚比绍",3.6),
    CountryAndSquare("比利时-卢森堡",3.3),
    CountryAndSquare("亚美尼亚",3.0),
    CountryAndSquare("莱索托",3.0),
    CountryAndSquare("阿尔巴尼亚",2.9),
    CountryAndSquare("所罗门群岛",2.9),
    CountryAndSquare("布隆迪",2.8),
    CountryAndSquare("赤道几内亚",2.8),
    CountryAndSquare("海地",2.8),
    CountryAndSquare("卢旺达",2.6),
    CountryAndSquare("吉布提",2.3),
    CountryAndSquare("伯利兹",2.3),
    CountryAndSquare("以色列",2.1),
    CountryAndSquare("萨尔瓦多",2.1),
    CountryAndSquare("斯洛文尼亚",2.0),
    CountryAndSquare("新喀里多尼亚",1.9),
    CountryAndSquare("科威特",1.8),
    CountryAndSquare("斐济",1.8),
    CountryAndSquare("斯威士兰",1.7),
    CountryAndSquare("东帝汶",1.5),
    CountryAndSquare("巴哈马",1.4),
    CountryAndSquare("瓦努阿图",1.2),
    CountryAndSquare("卡塔尔",1.1),
    CountryAndSquare("冈比亚",1.1),
    CountryAndSquare("牙买加",1.1),
    CountryAndSquare("黎巴嫩",1.0),
    CountryAndSquare("塞浦路斯",0.9),
    CountryAndSquare("波多黎各",0.9),
    CountryAndSquare("文莱",0.6),
    CountryAndSquare("佛得角",0.4),
    CountryAndSquare("萨摩亚",0.3),
    CountryAndSquare("科摩罗",0.2),
    CountryAndSquare("毛里求斯",0.2),
    CountryAndSquare("香港",0.1),
    CountryAndSquare("新加坡",0.1),
    CountryAndSquare("塞舌尔",0.1),
    CountryAndSquare("关岛",0.1),
    CountryAndSquare("巴林",0.1),
    CountryAndSquare("汤加",0.1),
    CountryAndSquare("安提瓜和巴布达",0.04),
    CountryAndSquare("巴巴多斯",0.04),
    CountryAndSquare("格林纳达",0.03),
    CountryAndSquare("马尔他",0.03)
]


private class CountryAndSquare {
    private let name:String
    private let square:Float64
    
    init(_ nameOfCountry:String, _ squareOfCountry:Float64) {
        self.name = nameOfCountry
        self.square = squareOfCountry
    }
    
    fileprivate static func sizeOfCountryDescription(countOfTerritory:Int) -> String {
        let sizeOfTerritory = square_of_each_location * Float64(countOfTerritory)
        var index = squares_of_all_countries.count - 1
        while true {
            let squareOfIndexCountry = squares_of_all_countries[index].square * 10000 // 单位是平方千米
            if squareOfIndexCountry > sizeOfTerritory || index == 0 {
                let rate = sizeOfTerritory / squareOfIndexCountry
                
                return String(format: "%.2f个%@", rate, squares_of_all_countries[index].name)
            } else {
                index = index - 1
            }
        }
    }
    
}

private let square_of_each_location:Float64 = Float64(510067866) / Float64(36000 * 18000)
*/
