//
//  DGRankView.swift
//  DiceGameLib
//
//  Created by apple on 15/7/1.
//  Copyright (c) 2015年 WhaleStudio. All rights reserved.
//

import UIKit

open class DGRankView : UIView, UITableViewDelegate, UITableViewDataSource {
    public static let SCORE_COLUMN_NAME_WINS = "wins"
    public static let SCORE_COLUMN_NAME_ATTACKS = "attacks"
    public static let SCORE_COLUMN_NAME_DEFENDS = "defends"
    
    fileprivate var rankTableView : UITableView!
    
    fileprivate let action2GetScoreFromDictionary:(([String:AnyObject]) -> Int)
    
    fileprivate var top10Dictionary:[[String:AnyObject]]!
    fileprivate var myUUID:String!
    fileprivate var myPlayerName:String!
    fileprivate var myRank:Int!
    fileprivate var myScore:Int!
    
    public init(frame: CGRect, columnName2Display4Score:String, action2GetScoreFromDictionary:@escaping (([String:AnyObject]) -> Int)) {
        self.action2GetScoreFromDictionary = action2GetScoreFromDictionary
        
        super.init(frame:frame)
        
        let viewAsBackgroundOfColumnNameLabels = UIView(frame: CGRect(x: 0, y: 0, width: frame.size.width, height: HEIGHT_OF_RANK_COLUMN))
        self.addSubview(viewAsBackgroundOfColumnNameLabels)
        viewAsBackgroundOfColumnNameLabels.backgroundColor = COLOR_OF_COLUMN_NAMES
        
        let rankColumnPlayerNameLabel = UILabel(frame:CGRect(x: MARGIN_OF_RANK_TABLE_VIEW + WIDTH_OF_FLAG + PADDING_BETWEEN_FLAG_AND_PLAYER_NAME, y: 0, width: frame.size.width -  WIDTH_OF_SCORE_LABEL - MARGIN_OF_RANK_TABLE_VIEW * 2 - WIDTH_OF_FLAG - PADDING_BETWEEN_FLAG_AND_PLAYER_NAME, height: HEIGHT_OF_RANK_COLUMN))
        self.addSubview(rankColumnPlayerNameLabel)
        rankColumnPlayerNameLabel.text = DGBundle.i18n(key:"Player")
        rankColumnPlayerNameLabel.textAlignment = NSTextAlignment.left
        rankColumnPlayerNameLabel.backgroundColor = UIColor.clear
        rankColumnPlayerNameLabel.textColor = DGColors.LABEL_COLOR

        let rankColumnSteakLabel = UILabel(frame:CGRect(x: frame.size.width - WIDTH_OF_SCORE_LABEL - MARGIN_OF_RANK_TABLE_VIEW, y: 0, width: WIDTH_OF_SCORE_LABEL, height: HEIGHT_OF_RANK_COLUMN))
        self.addSubview(rankColumnSteakLabel)
        rankColumnSteakLabel.text = columnName2Display4Score
        rankColumnSteakLabel.backgroundColor = UIColor.clear
        rankColumnSteakLabel.textColor = DGColors.LABEL_COLOR
        rankColumnSteakLabel.textAlignment = NSTextAlignment.center
    }

    required public init(coder aDecoder: NSCoder) {
        fatalError("init(coder:) has not been implemented")
    }
    
    open func setDataSource(top10Dictionary:[[String:AnyObject]],
        myUUID:String, myPlayerName:String, myRank:Int, myScore:Int) {
            self.top10Dictionary = top10Dictionary
            self.myUUID = myUUID
            self.myPlayerName = myPlayerName
            self.myRank = myRank
            self.myScore = myScore
            
            self.rankTableView = UITableView(frame:CGRect(x: 0, y: HEIGHT_OF_RANK_COLUMN, width: self.bounds.size.width, height: self.bounds.size.height-HEIGHT_OF_RANK_COLUMN), style: UITableView.Style.plain)
            self.addSubview(self.rankTableView)
            self.rankTableView.backgroundColor = UIColor.clear
            self.rankTableView.delegate = self
            self.rankTableView.dataSource = self
            
            self.rankTableView.reloadData()
    }
    
    fileprivate func amIOfTop10() -> Bool {
        for mapData in self.top10Dictionary {
            let uuidOfTop10Member = mapData[SCORE_COLUMN_NAME_UUID] as! String
            if uuidOfTop10Member == self.myUUID {
                return true
            }
        }
        
        return false
    }
    
    @objc open func tableView(_ tableView: UITableView, numberOfRowsInSection section: Int) -> Int {
        var returnCount = self.top10Dictionary.count
        if !self.amIOfTop10() {
            returnCount += 1
        }
        
        return returnCount
    }
    
    
    @objc open func tableView(_ tableView: UITableView, cellForRowAt indexPath: IndexPath) -> UITableViewCell {
        let row = (indexPath as NSIndexPath).row
        let reuseIdentifier = "DGTop10RankDataSource_TableViewCell\(row)"

        let name:String, score:Int, rank:Int, isMine:Bool
        
        if row < self.top10Dictionary.count {
            let currentRowDictionary = self.top10Dictionary[row]
            name = currentRowDictionary[SCORE_COLUMN_NAME_PLAYER_NAME] as! String
            score = self.action2GetScoreFromDictionary(currentRowDictionary)
            rank = row + 1
            let currentRowUUID = currentRowDictionary[SCORE_COLUMN_NAME_UUID] as! String
            isMine = (currentRowUUID == self.myUUID)
        } else {
            name = self.myPlayerName
            score = self.myScore
            rank = self.myRank
            isMine = true
        }
        
        if let cell = tableView.dequeueReusableCell(withIdentifier: reuseIdentifier) {
            self.decorateCell(cell, name: name, score: score, rank: rank, isMine: isMine)
            return cell
        } else {
            let cell = UITableViewCell(style: UITableViewCell.CellStyle.default, reuseIdentifier: reuseIdentifier)
            self.decorateCell(cell, name: name, score: score, rank: rank, isMine: isMine)
            return cell
        }
    }
    
    open func tableView(_ tableView: UITableView, heightForRowAt indexPath: IndexPath) -> CGFloat {
        return HEIGHT_OF_TABLE_CELL_VIEW
    }
    
    fileprivate func decorateCell(_ cell:UITableViewCell, name:String, score:Int, rank:Int, isMine:Bool) {
        cell.backgroundColor = UIColor.clear
        cell.isUserInteractionEnabled = false
        
        let shadowLayerView = UIView(frame:CGRect(x: MARGIN_OF_RANK_TABLE_VIEW + WIDTH_OF_FLAG_CORNER, y: MARGIN_OF_TABLE_CELL_VIEW, width: self.rankTableView.frame.size.width - MARGIN_OF_RANK_TABLE_VIEW * 2 - WIDTH_OF_FLAG_CORNER, height: HEIGHT_OF_TABLE_CELL_VIEW - MARGIN_OF_TABLE_CELL_VIEW * 2))
        cell.addSubview(shadowLayerView)
        shadowLayerView.backgroundColor = isMine ? COLOR_OF_COLUMN_NAMES : UIColor.white
        shadowLayerView.layer.shadowOffset = CGSize(width: 3, height: 3)
        shadowLayerView.layer.shadowColor = UIColor.gray.cgColor
        shadowLayerView.layer.shadowOpacity = 1
        
        let flagImageView = UIImageView(image: getImageByRank(rank))
        flagImageView.frame = CGRect(x: MARGIN_OF_RANK_TABLE_VIEW, y: MARGIN_OF_TABLE_CELL_VIEW, width: WIDTH_OF_FLAG, height: HEIGHT_OF_TABLE_CELL_VIEW - MARGIN_OF_TABLE_CELL_VIEW * 2)
        cell.addSubview(flagImageView)
        
        let rankLabel = UILabel(frame:CGRect(x: MARGIN_OF_RANK_TABLE_VIEW, y: MARGIN_OF_TABLE_CELL_VIEW, width: WIDTH_OF_FLAG, height: HEIGHT_OF_TABLE_CELL_VIEW - MARGIN_OF_TABLE_CELL_VIEW * 2))
        cell.addSubview(rankLabel)
        rankLabel.text = String(rank)
        rankLabel.adjustsFontSizeToFitWidth = true
        rankLabel.textAlignment = NSTextAlignment.center
        rankLabel.font = UIFont(name: "Helvetica", size: WIDTH_OF_FLAG)
        rankLabel.textColor = DGColors.LABEL_COLOR
        
        let playerNameLabel = UILabel(frame: CGRect(x: MARGIN_OF_RANK_TABLE_VIEW + WIDTH_OF_FLAG + PADDING_BETWEEN_FLAG_AND_PLAYER_NAME, y: MARGIN_OF_TABLE_CELL_VIEW, width: self.rankTableView.bounds.size.width - MARGIN_OF_RANK_TABLE_VIEW * 2 - WIDTH_OF_SCORE_LABEL - WIDTH_OF_FLAG - PADDING_BETWEEN_FLAG_AND_PLAYER_NAME, height: HEIGHT_OF_TABLE_CELL_VIEW - MARGIN_OF_TABLE_CELL_VIEW * 2))
        cell.addSubview(playerNameLabel)
        playerNameLabel.text = name
        playerNameLabel.textAlignment = NSTextAlignment.left
        playerNameLabel.textColor = isMine ? DGColors.LABEL_COLOR : UIColor.black

        let scoreLabel = UILabel(frame:CGRect(x: MARGIN_OF_RANK_TABLE_VIEW + self.rankTableView.bounds.size.width - MARGIN_OF_RANK_TABLE_VIEW * 2 - WIDTH_OF_SCORE_LABEL, y: MARGIN_OF_TABLE_CELL_VIEW, width: WIDTH_OF_SCORE_LABEL, height: HEIGHT_OF_TABLE_CELL_VIEW - MARGIN_OF_TABLE_CELL_VIEW * 2))
        cell.addSubview(scoreLabel)
        scoreLabel.text = String(score)
        scoreLabel.textAlignment = NSTextAlignment.center
        scoreLabel.textColor = isMine ? DGColors.LABEL_COLOR : UIColor.red
    }
}

private let SCORE_COLUMN_NAME_UUID = "uuid"
private let SCORE_COLUMN_NAME_PLAYER_NAME = "name"

private let HEIGHT_OF_RANK_COLUMN:CGFloat = 30
private let MARGIN_OF_RANK_TABLE_VIEW:CGFloat = 10

private let HEIGHT_OF_TABLE_CELL_VIEW:CGFloat = 50
private let MARGIN_OF_TABLE_CELL_VIEW:CGFloat = 5
private let WIDTH_OF_FLAG:CGFloat = 20
private let WIDTH_OF_FLAG_CORNER:CGFloat = 7
private let PADDING_BETWEEN_FLAG_AND_PLAYER_NAME:CGFloat = 5
private let WIDTH_OF_SCORE_LABEL:CGFloat = 120

//private let COLOR_OF_COLUMN_NAMES = UIColor(red: 237 / 255, green: 13 / 255, blue: 82 / 255, alpha: 1.0)
private let COLOR_OF_COLUMN_NAMES = UIColor(red: 183 / 255, green: 64 / 255, blue: 221 / 255, alpha: 1.0)


private func getImageByRank(_ rank:Int) -> UIImage {
    if rank < FLAG_IMAGES.count {
        return FLAG_IMAGES[rank - 1]
    } else {
        return FLAG_IMAGES[3]
    }
}
private let FLAG_IMAGES = [
    UIImage(named: "flag1st.jpg")!,
    UIImage(named: "flag2nd.jpg")!,
    UIImage(named: "flag3rd.jpg")!,
    UIImage(named: "flagother.jpg")!
]



