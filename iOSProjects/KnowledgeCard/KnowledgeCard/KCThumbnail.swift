//
//  KCThumbnail.swift
//  KnowledgeCard
//
//  Created by alex on 2018/7/13.
//  Copyright © 2018年 WhaleStudio. All rights reserved.
//

import UIKit
import SnapKit

class KCThumbnailCollectionView:UICollectionView, UICollectionViewDataSource, UICollectionViewDelegateFlowLayout {
    var thumbnailDelegate:KCThumbnailCollectionViewDelegate!
    var thumbnailDataSource:KCDataSource!
    
    override init(frame: CGRect, collectionViewLayout layout: UICollectionViewLayout) {
        super.init(frame: frame, collectionViewLayout: layout)
        
        self.prepare()
    }
    
    required init?(coder aDecoder: NSCoder) {
        super.init(coder: aDecoder)
        
        self.prepare()
    }
    
    private func prepare() {
        self.dataSource = self
        self.delegate = self
        
        self.register(KCThumbnailCell.self, forCellWithReuseIdentifier: ID_CELL)
    }
    
    // MARK: - UICollectionViewDateSource
    // MARK: - UICollectionViewDelegateFlowLayout
    func numberOfSections(in collectionView: UICollectionView) -> Int {
        return 1
    }
    
    func collectionView(_ collectionView: UICollectionView, numberOfItemsInSection section: Int) -> Int {
        return self.thumbnailDataSource.datasourceCountOfThumbs()
    }
    
    func collectionView(_ collectionView: UICollectionView, cellForItemAt indexPath: IndexPath) -> UICollectionViewCell {
        let know = self.thumbnailDataSource.datasourceKnowledgeBy(index: indexPath.row)
        
        let cell = collectionView.dequeueReusableCell(withReuseIdentifier: ID_CELL, for: indexPath) as! KCThumbnailCell
        
        cell.setKnowledge(know)
        /*
        var selected = false
        if let theSelectedIndexPath = self.selectedItem {
            if theSelectedIndexPath.section == indexPath.section && theSelectedIndexPath.row == indexPath.row {
                selected = true
            }
        }
        cell.isSelected = selected
        */
        return cell
    }
    
    func collectionView(_ collectionView: UICollectionView, layout collectionViewLayout: UICollectionViewLayout, sizeForItemAt indexPath: IndexPath) -> CGSize {
        return SIZE_CELL
    }
    
    func collectionView(_ collectionView: UICollectionView, didSelectItemAt indexPath: IndexPath) {
        self.thumbnailDelegate.thumbnailCollectionViewDidSelect(indexOfThumbs: indexPath.row)
    }
    
    func collectionView(_ collectionView: UICollectionView, layout collectionViewLayout: UICollectionViewLayout, minimumLineSpacingForSectionAt section: Int) -> CGFloat {
        return 1
    }
    
    func collectionView(_ collectionView: UICollectionView, layout collectionViewLayout: UICollectionViewLayout, minimumInteritemSpacingForSectionAt section: Int) -> CGFloat {
        return 0
    }
    
    // MARK: - Instance Methods
}

protocol KCThumbnailCollectionViewDelegate {
    func thumbnailCollectionViewDidSelect(indexOfThumbs:Int)
}

private let ID_CELL = "KCThumbnailCell"
private let WIDTH_CELL = UIScreen.main.bounds.width / 3
private let HEIGHT_CELL = WIDTH_CELL / 2 * 3
private let SIZE_CELL = CGSize(width: WIDTH_CELL, height: HEIGHT_CELL)

private class KCThumbnailCell : UICollectionViewCell {
    private var largeButton:UIButton!
    
    func setKnowledge(_ know:KCKnowledge) {
        let knowView = know.asThumb()
        self.addSubview(knowView)
        
        knowView.snp.makeConstraints { (make) in
            make.edges.equalTo(self).inset(UIEdgeInsets.init(top: 0, left: 0, bottom: 0, right: 0))
        }
        
        let glassView = UIView()
        self.addSubview(glassView)
        glassView.snp.makeConstraints { (make) in
            make.edges.equalTo(self).inset(UIEdgeInsets.init(top: 0, left: 0, bottom: 0, right: 0))
        }
        
        /*
        
        self.largeButton = UIButton()
        self.addSubview(self.largeButton)
        self.largeButton.snp.makeConstraints { (make) in
            make.size.equalTo(CGSize(width: 20, height: 20))
            make.top.equalTo(self).offset(5)
            make.right.equalTo(self).offset(-5)
        }
        self.largeButton.setImage(UIImage(named: "large_1024.png"), for: .normal)
        self.largeButton.isHidden = true
 */
    }
    
    /*
    override var isSelected: Bool {
        willSet {
            onSelected(newValue)
        }
    }
    
    private func onSelected(_ selected:Bool) {
        let layer = self.layer
        
        if selected {
            layer.masksToBounds = true
            layer.borderWidth = 1
            layer.borderColor = UIColor.red.cgColor
            
            self.largeButton.isHidden = false
        } else {
            layer.borderWidth = 0
            
            self.largeButton.isHidden = true
        }
    }
    */
    
}
