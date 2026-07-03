//
//  MovePickerViewController.swift
//  Gym
//
//  Created by alex on 2018/1/15.
//  Copyright © 2018年 WhaleStudio. All rights reserved.
//

import UIKit

class MovePickerViewController : UIViewController, UITableViewDelegate, UITableViewDataSource {
    @IBOutlet weak var categoryTableView: UITableView!
    @IBOutlet weak var movesTableView: UITableView!
    
    var delegate:MovePickerViewControllerDelegate!
    var indexOfMoveInTraining:Int!
    
    override func viewDidLoad() {
        self.categoryTableView.delegate = self
        self.categoryTableView.dataSource = self
        
        self.movesTableView.delegate = self
        self.movesTableView.dataSource = self
        
        self.categoryTableView.register(CellOfCategoryTableView.self, forCellReuseIdentifier: CATEGORY_TABLEVIEW_CELL_ID)
        self.movesTableView.register(CellOfMovesTableView.self, forCellReuseIdentifier: MOVES_TABLEVIEW_CELL_ID)
        
        super.viewDidLoad()
    }
    
    @IBAction func onSureButtonPressed() {
        if let selectedIndexPath = self.movesTableView.indexPathForSelectedRow {
            self.dismiss(animated: true, completion: {
                let selectedMove = GCenter.instance.nameOfMoveBy(indexOfCategory: selectedIndexPath.section, indexOfMove: selectedIndexPath.row)
                self.delegate.movePickerViewControllerAfterSelect(move: selectedMove, indexOfMoveInTraining: self.indexOfMoveInTraining)
            })
        }
    }
    
    // MARK: - UITableViewDelegate, UITableViewDataSource
    func numberOfSections(in tableView: UITableView) -> Int {
        if tableView == self.categoryTableView {
            return 1
        }
        
        return GCenter.instance.countOfCategories()
    }
    
    func tableView(_ tableView: UITableView, numberOfRowsInSection section: Int) -> Int {
        if tableView == self.categoryTableView {
            return GCenter.instance.countOfCategories()
        }
        
        return GCenter.instance.countOfMovesBy(indexOfCategory: section)
    }
    
    func tableView(_ tableView: UITableView, heightForHeaderInSection section: Int) -> CGFloat {
        if tableView == self.categoryTableView {
            return 0
        }
        
        return HEIGHT_OF_HEADER_OF_MOVES_TABLEVIEW
    }
    
    func tableView(_ tableView: UITableView, viewForHeaderInSection section: Int) -> UIView? {
        if tableView == self.categoryTableView {
            return nil
        }
        
        let header = HeaderOfMovesTableView(frame: CGRect(x: 0, y: 0, width: tableView.bounds.width, height: HEIGHT_OF_HEADER_OF_MOVES_TABLEVIEW))
        header.label.text = GCenter.instance.nameOfCategoryBy(index: section)
        
        return header
    }
    
    func tableView(_ tableView: UITableView, heightForRowAt indexPath: IndexPath) -> CGFloat {
        if tableView == self.categoryTableView {
            return tableView.bounds.height / CGFloat(GCenter.instance.countOfCategories())
        }
        
        return HEIGHT_OF_CELL_MOVES_TABLEVIEW
    }
    
    func tableView(_ tableView: UITableView, cellForRowAt indexPath: IndexPath) -> UITableViewCell {
        if tableView == self.categoryTableView {
            let categoryCell:CellOfCategoryTableView
            if let cell = tableView.dequeueReusableCell(withIdentifier: CATEGORY_TABLEVIEW_CELL_ID) as? CellOfCategoryTableView {
                categoryCell = cell
            } else {
                categoryCell = CellOfCategoryTableView(style: UITableViewCell.CellStyle.default, reuseIdentifier: CATEGORY_TABLEVIEW_CELL_ID)
            }
            
            categoryCell.textLabel?.text = GCenter.instance.nameOfCategoryBy(index: indexPath.row)
            
            return categoryCell
        }
        
        let moveCell:CellOfMovesTableView
        if let cell = tableView.dequeueReusableCell(withIdentifier: MOVES_TABLEVIEW_CELL_ID) as? CellOfMovesTableView {
            moveCell = cell
        } else {
            moveCell = CellOfMovesTableView(style: .default, reuseIdentifier: MOVES_TABLEVIEW_CELL_ID)
        }
        
        moveCell.textLabel?.text = GCenter.instance.nameOfMoveBy(indexOfCategory: indexPath.section, indexOfMove: indexPath.row)
        
        return moveCell
    }
    
    func tableView(_ tableView: UITableView, didSelectRowAt indexPath: IndexPath) {
        if tableView == self.categoryTableView {
            self.movesTableView.selectRow(at: IndexPath(row: 0, section: indexPath.row), animated: true, scrollPosition: .top)
            return
        }
        
        self.categoryTableView.selectRow(at: IndexPath(row: indexPath.section, section: 0), animated: true, scrollPosition: .middle)
    }
    
    func tableView(_ tableView: UITableView, editActionsForRowAt indexPath: IndexPath) -> [UITableViewRowAction]? {
        if tableView == self.categoryTableView {
            return nil
        }
        
        let insertAction = UITableViewRowAction(style: .destructive, title: "插入", handler: { (action, ip) in
            self.addMoveAction(indexOfCategory: ip.section, atIndexOfMove: ip.row)
        })
        insertAction.backgroundColor = UIColor.green
        let deleteAction = UITableViewRowAction(style: .destructive, title: "删除", handler: { (action, ip) in
            self.deleteMoveAction(indexOfCategory: ip.section, indexOfMove: ip.row)
        })
        deleteAction.backgroundColor = UIColor.red
        
        return [
            insertAction, deleteAction
        ]
    }
    
    /*
    func tableView(_ tableView: UITableView, canEditRowAt indexPath: IndexPath) -> Bool {
        if tableView == self.categoryTableView {
            return false
        }
        
        return true
    }
 */
 
    /*
    func tableView(_ tableView: UITableView, commit editingStyle: UITableViewCellEditingStyle, forRowAt indexPath: IndexPath) {
        if tableView == self.categoryTableView {
            return
        } else if tableView == self.movesTableView {
            switch editingStyle {
            case .insert:
                print("insert")
            case .delete:
                print("delete")
            default:
                print("others")
            }
        }
    }
 */
    // MARK: - Private Methods
    private func addMoveAction(indexOfCategory:Int, atIndexOfMove indexOfMove:Int) {
        let alertVC = UIAlertController(title: "添加动作", message: nil, preferredStyle: UIAlertController.Style.alert)
        let cancelAction = UIAlertAction(title: "取消", style: UIAlertAction.Style.cancel) { (action) in
            // 取消操作
        }
        let yesAction = UIAlertAction(title: "确定", style: UIAlertAction.Style.default) { (action) in
            // 确定操作
            let nameOfNewMoveTF = (alertVC.textFields?.first)!
            if GCenter.instance.add(nameOfMove: nameOfNewMoveTF.text!, byIndexOfCategory: indexOfCategory, atIndexOfMove: indexOfMove) {
                self.movesTableView.reloadData()
                self.movesTableView.selectRow(at: IndexPath(row: indexOfMove, section: indexOfCategory), animated: true, scrollPosition: .none)
                self.categoryTableView.selectRow(at: IndexPath(row: indexOfCategory, section: 0), animated: true, scrollPosition: .none)
            }
        }
        alertVC.addTextField { (tf) in
            tf.placeholder = "新动作"
        }
        alertVC.addAction(cancelAction)
        alertVC.addAction(yesAction)
        
        self.present(alertVC, animated: true, completion: nil)
    }
    
    private func deleteMoveAction(indexOfCategory: Int, indexOfMove: Int) {
        GCenter.instance.deleteMoveBy(indexOfCategory: indexOfCategory, andIndexOfMove: indexOfMove)
        
        self.movesTableView.reloadData()
    }
    
    // MARK: - Private Methods
    func setSelected(nameOfMove:String, indexOfMoveInTraining:Int) {
        self.indexOfMoveInTraining = indexOfMoveInTraining
        
        if let (indexOfCategory, indexOfMove) = GCenter.instance.indexPathFor(nameOfMove: nameOfMove) {
            self.movesTableView.selectRow(at: IndexPath(row: indexOfMove, section: indexOfCategory), animated: true, scrollPosition: .middle)
            self.categoryTableView.selectRow(at: IndexPath(row: indexOfCategory, section: 0), animated: true, scrollPosition: .none)
        }
    }
}

fileprivate let HEIGHT_OF_HEADER_OF_MOVES_TABLEVIEW : CGFloat = 30
fileprivate class HeaderOfMovesTableView : UIView {
    fileprivate var label:UILabel!
    
    override init(frame: CGRect) {
        super.init(frame: frame)
        
        self.label = UILabel(frame:self.bounds)
        self.addSubview(self.label)
        self.label.textAlignment = .center
    }
    
    required init?(coder aDecoder: NSCoder) {
        fatalError("init(coder:) has not been implemented")
    }
}

fileprivate let HEIGHT_OF_CELL_MOVES_TABLEVIEW : CGFloat = 30
fileprivate let CATEGORY_TABLEVIEW_CELL_ID = "CATEGORY_TABLEVIEW_CELL_ID"
fileprivate class CellOfCategoryTableView : UITableViewCell {
    override init(style: UITableViewCell.CellStyle, reuseIdentifier: String?) {
        super.init(style: style, reuseIdentifier: reuseIdentifier)
    }
    
    required init?(coder aDecoder: NSCoder) {
        fatalError("init(coder:) has not been implemented")
    }
}

fileprivate let MOVES_TABLEVIEW_CELL_ID = "MOVES_TABLEVIEW_CELL_ID"
fileprivate class CellOfMovesTableView : UITableViewCell {
    override init(style: UITableViewCell.CellStyle, reuseIdentifier: String?) {
        super.init(style: style, reuseIdentifier: reuseIdentifier)
    }
    
    required init?(coder aDecoder: NSCoder) {
        fatalError("init(coder:) has not been implemented")
    }
}

protocol MovePickerViewControllerDelegate {
    func movePickerViewControllerAfterSelect(move:String, indexOfMoveInTraining:Int)
}
