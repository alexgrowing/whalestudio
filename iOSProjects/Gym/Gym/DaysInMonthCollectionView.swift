//
//  DaysCollectionView.swift
//  Gym
//
//  Created by alex on 2018/1/25.
//  Copyright © 2018年 WhaleStudio. All rights reserved.
//

import UIKit
import WhaleLib

class DaysInMonthCollectionView : UICollectionView, UICollectionViewDataSource, UICollectionViewDelegateFlowLayout, DayOfDaysCollectionViewDelegate {
    private var currentYear:Int!
    private var currentMonth:Int!
    private var firstCellDay:SimpleDate!
    
    var delegateOfDateEdit:DayOfDaysCollectionViewDelegate!
    
    init() {
        super.init(frame: CGRect(x: 0, y: 0, width: 0, height: 0), collectionViewLayout: UICollectionViewFlowLayout())
                
        self.dataSource = self
        self.delegate = self
        
        self.register(HeaderOfDaysCollectionView.self, forSupplementaryViewOfKind: UICollectionView.elementKindSectionHeader, withReuseIdentifier: ID_HEAD_CELL)
        self.register(DayOfDaysCollectionView.self, forCellWithReuseIdentifier: ID_CELL)
    }
    
    required init?(coder aDecoder: NSCoder) {
        fatalError("init(coder:) has not been implemented")
    }
    
    // MARK: - UICollectionViewDateSource
    // MARK: - UICollectionViewDelegateFlowLayout
    func numberOfSections(in collectionView: UICollectionView) -> Int {
        return 1
    }
    
    func collectionView(_ collectionView: UICollectionView, numberOfItemsInSection section: Int) -> Int {
        return 7 * 6
    }
    
    func collectionView(_ collectionView: UICollectionView, viewForSupplementaryElementOfKind kind: String, at indexPath: IndexPath) -> UICollectionReusableView {
        return collectionView.dequeueReusableSupplementaryView(ofKind: kind, withReuseIdentifier: ID_HEAD_CELL, for: indexPath)
    }
    
    func collectionView(_ collectionView: UICollectionView, cellForItemAt indexPath: IndexPath) -> UICollectionViewCell {
        let cell = collectionView.dequeueReusableCell(withReuseIdentifier: ID_CELL, for: indexPath) as! DayOfDaysCollectionView
        cell.delegate = self
        let dateOfCell = self.firstCellDay.plus(days: indexPath.row)
        cell.set(date: dateOfCell, isCurrentMonth: dateOfCell.year == self.currentYear && dateOfCell.month == self.currentMonth)
        
        return cell
    }
    
    func collectionView(_ collectionView: UICollectionView, layout collectionViewLayout: UICollectionViewLayout, referenceSizeForHeaderInSection section: Int) -> CGSize {
        return CGSize(width: UIScreen.main.bounds.width, height: HEIGHT_OF_HEADER_OF_COLLECTION_VIEW)
    }
    
    func collectionView(_ collectionView: UICollectionView, layout collectionViewLayout: UICollectionViewLayout, sizeForItemAt indexPath: IndexPath) -> CGSize {
        // 宽度减1,留一些空间出来显示边框
        return CGSize(width: Int(UIScreen.main.bounds.width / 7) - 1, height: Int((collectionView.frame.height - HEIGHT_OF_HEADER_OF_COLLECTION_VIEW) / 6) - 1)
    }
    
    // 两行cell之间的间距（上下行cell的间距）
    func collectionView(_ collectionView: UICollectionView, layout collectionViewLayout: UICollectionViewLayout, minimumLineSpacingForSectionAt section: Int) -> CGFloat {
        return 1
    }
    
    // 两个cell之间的间距（同一行的cell的间距）
    func collectionView(_ collectionView: UICollectionView, layout collectionViewLayout: UICollectionViewLayout, minimumInteritemSpacingForSectionAt section: Int) -> CGFloat {
        return 0
    }
    
    // MARK: - DayOfDaysCollectionViewDelegate
    func editContentOfDate(date: SimpleDate) {
        self.delegateOfDateEdit.editContentOfDate(date: date)
    }
    
    // MARK: - Instance Methods
    func resetBy(currentYear:Int, currentMonth:Int) {
        self.currentYear = currentYear
        self.currentMonth = currentMonth
        self.firstCellDay = Utils.firstMonthCellDay(year: self.currentYear, month: self.currentMonth, isChinese: true)
        
        self.reloadData()
    }
    
    func getCurrentMonth() -> (year:Int, month:Int) {
        return (self.currentYear, self.currentMonth)
    }
}



private let ID_HEAD_CELL = "ID_OF_HEAD_CELL"
private let HEIGHT_OF_HEADER_OF_COLLECTION_VIEW : CGFloat = 30

private class HeaderOfDaysCollectionView : UICollectionViewCell {
    override init(frame: CGRect) {
        super.init(frame: frame)
        
        self.backgroundColor = UIColor.lightGray
        
        let weeks = ["一", "二", "三", "四", "五", "六", "日"]
        let widthOfEachLabel = Int(self.contentView.bounds.width / CGFloat(weeks.count))
        for i in 0 ..< weeks.count {
            let label = UILabel(frame: CGRect(x: i * widthOfEachLabel, y: 0, width: widthOfEachLabel, height: Int(self.contentView.bounds.height)))
            self.contentView.addSubview(label)
            label.textAlignment = .center
            label.text = weeks[i]
        }
    }
    
    required init?(coder aDecoder: NSCoder) {
        fatalError("init(coder:) has not been implemented")
    }
}

private let ID_CELL = "ID_OF_DAYS_CELL_COLLECTION"
fileprivate class DayOfDaysCollectionView : UICollectionViewCell {
    var delegate:DayOfDaysCollectionViewDelegate!
    private var date:SimpleDate!
    
    private var numberLabel:UILabel!
    private var dumbImageButton:UIButton!
    
    override init(frame: CGRect) {
        super.init(frame: frame)
        self.contentView.backgroundColor = UIColor.white
        
        let size_of_number_label:CGFloat = 24
        self.numberLabel = UILabel(frame:CGRect(x: (self.contentView.bounds.width - size_of_number_label)/2, y: 0, width: size_of_number_label, height: size_of_number_label))
        self.contentView.addSubview(self.numberLabel)
        self.numberLabel.textAlignment = .center
        self.numberLabel.layer.cornerRadius = size_of_number_label / 2
        self.numberLabel.clipsToBounds = true
        self.numberLabel.backgroundColor = UIColor.white
        
        let width_of_button = self.contentView.bounds.width
        let height_of_button = self.contentView.bounds.height - size_of_number_label
        self.dumbImageButton = UIButton(frame:CGRect(x: 0, y: size_of_number_label, width: width_of_button, height: height_of_button))
        self.contentView.addSubview(self.dumbImageButton)
        self.dumbImageButton.setImage(nil, for: .normal)
        let size_of_image = min(width_of_button, height_of_button) / 4 * 3
        self.dumbImageButton.imageEdgeInsets = UIEdgeInsets(top: (height_of_button - size_of_image)/2, left: (width_of_button - size_of_image)/2, bottom: (height_of_button - size_of_image)/2, right: (width_of_button - size_of_image)/2)
        self.dumbImageButton.setBackgroundImage(WLUI.drawColorAsImage(color: UIColor(red: 229/255, green: 231/255, blue: 228/255, alpha: 1.0)), for: .highlighted)
        
        self.dumbImageButton.addTarget(self, action: #selector(openDetailsOfTraining), for: .touchUpInside)
    }
    
    required init?(coder aDecoder: NSCoder) {
        fatalError("init(coder:) has not been implemented")
    }
    
    fileprivate func set(date:SimpleDate, isCurrentMonth:Bool) {
        self.date = date
        self.numberLabel.text = String(self.date.day)
        
        if GCenter.instance.getTrainingBy(date: self.date) != nil {
            self.dumbImageButton.setImage(UIImage(named: "dumbbell.png"), for: .normal)
        } else {
            self.dumbImageButton.setImage(nil, for: .normal)
        }
        
        if isCurrentMonth {
            self.numberLabel.textColor = UIColor.black
        } else {
            self.numberLabel.textColor = UIColor.black.withAlphaComponent(0.3)
        }
        
        let dcOfToday = Calendar.current.dateComponents([.year, .month, .day], from: Date())
        if dcOfToday.year == date.year && dcOfToday.month == date.month && dcOfToday.day == date.day {
            self.numberLabel.textColor = UIColor.white
            self.numberLabel.backgroundColor = UIColor.red
        } else {
            self.numberLabel.backgroundColor = UIColor.white
        }
    }
    
    @objc func openDetailsOfTraining() {
        self.delegate.editContentOfDate(date: self.date)
    }
}

protocol DayOfDaysCollectionViewDelegate {
    func editContentOfDate(date:SimpleDate)
}
