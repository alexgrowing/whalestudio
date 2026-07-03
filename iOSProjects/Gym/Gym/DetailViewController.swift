//
//  DetailViewController.swift
//  Gym
//
//  Created by alex on 2017/10/29.
//  Copyright © 2017年 WhaleStudio. All rights reserved.
//

import UIKit
import WhaleLib

class DetailViewController: UIViewController, UITableViewDelegate, UITableViewDataSource, WLKeyboardToolbarDelegate, MoveCellViewDelegate, MovePickerViewControllerDelegate, GlassViewDelegate, UITextViewDelegate {
    var training:GTraining! {
        didSet {
            self.populateTraining(selectedIndex: -1)
        }
    }
    var delegate:DetailViewControllerDelegate!
    
    @IBOutlet weak var dateButton: UIButton!
    @IBOutlet weak var movesTableView: UITableView!
    @IBOutlet weak var feelingTextView: UITextView!
    
    @IBOutlet weak var gap2Bottom: NSLayoutConstraint!
    private var toolbar4Keyboard:WLKeyboardToolbar!
    private var glass4Keyboard:GlassView!
    
    @IBAction func addMoveButtonPressed() {
        let newMove:GMove
        if self.training.moves.count == 0 {
            newMove = GMove(name: "山羊挺身", weight: 10, times: 30)
            
            self.training.moves.append(newMove)
            self.editNameOfMoveBy(indexOfMove: 0)
        } else {
            self.training.moves.append(self.training.moves.last!.clone())
            self.populateTraining(selectedIndex: self.training.moves.count - 1)
        }
    }
    
    @IBAction func back() {
        self.dismiss(animated: true, completion: {
            self.delegate.onSaveDetailViewController(newTraining: self.training)
        })
    }
    
    override func viewDidLoad() {
        super.viewDidLoad()
        
        self.movesTableView.register(MoveCellView.self, forCellReuseIdentifier: MOVE_CELL_VIEW_ID)
        self.movesTableView.rowHeight = MOVE_CELL_VIEW_HEIGHT_OF_ROW
        
        self.setup()
    }
    
    override func viewWillAppear(_ animated: Bool) {
        NotificationCenter.default.addObserver(self, selector: #selector(keyboardWillShow(_:)), name: UIResponder.keyboardWillShowNotification, object: nil)
        NotificationCenter.default.addObserver(self, selector: #selector(keyboardWillHide(_:)), name: UIResponder.keyboardWillHideNotification, object: nil)
        
        super.viewWillAppear(animated)
    }
    
    override func viewWillDisappear(_ animated: Bool) {
        NotificationCenter.default.removeObserver(self)
        
        super.viewWillDisappear(animated)
    }
    
    @objc func keyboardWillShow(_ notification: Notification) {
        guard let fr = UIResponder.firstResponder() else {
            return
        }
        
        let dict = NSDictionary(dictionary: notification.userInfo!)
        let keyboardFrame = dict[UIResponder.keyboardFrameEndUserInfoKey] as! CGRect
        
        let yPointOfToolbar = keyboardFrame.origin.y - WLKeyboardToolbar.HEIGHT_OF_KEYBOARD_TOOLBAR

        self.toolbar4Keyboard.moveTo(yPoint: yPointOfToolbar)
        if fr === self.feelingTextView {
            self.glass4Keyboard.frame = CGRect(x: 0, y: 0, width: UIScreen.main.bounds.width, height: yPointOfToolbar - fr.bounds.height)
        } else {
            self.glass4Keyboard.frame = CGRect(x: 0, y: 0, width: UIScreen.main.bounds.width, height: yPointOfToolbar)
        }
        
        let origin2ScreenOfFirstResponder = fr.convert(CGPoint.zero, to: self.view)
        let bottomOfFirstResponder = origin2ScreenOfFirstResponder.y + fr.bounds.size.height + self.gap2Bottom.constant
        
        if bottomOfFirstResponder > yPointOfToolbar {
            self.gap2Bottom.constant = bottomOfFirstResponder - yPointOfToolbar
            self.view.layoutIfNeeded()
        }
        
        /*
        self.glassViewOnEditingFeeling.frame = CGRect(x: 0, y: 0, width: UIScreen.main.bounds.width, height: yPointOfToolbar - self.feelingTextView.frame.size.height)
        
        let originOfFeelingTextView2Screen = self.feelingTextView.convert(CGPoint(x: 0, y: 0), to:self.view)
        let bottomOfFeelingTextView2Screen = originOfFeelingTextView2Screen.y + self.feelingTextView.frame.size.height
        self.gap2Bottom.constant = bottomOfFeelingTextView2Screen - yPointOfToolbar
        
        self.view.layoutIfNeeded()
 */
    }
    
    @objc func keyboardWillHide(_ notification: Notification) {
        self.gap2Bottom.constant = 0
        self.view.layoutIfNeeded()
    }
    
    // MARK: - UITextViewDelegate
    func textViewDidEndEditing(_ textView: UITextView) {
        self.training.feeling = self.feelingTextView.text!
    }
    
    // MARK: - UITableViewDelegate
    // MARK: - UITableViewDataSource
    func tableView(_ tableView: UITableView, numberOfRowsInSection section: Int) -> Int {
        if self.training != nil {
            return self.training.moves.count
        }
        
        return 0
    }
    
    func tableView(_ tableView: UITableView, heightForHeaderInSection section: Int) -> CGFloat {
        return MOVE_CELL_VIEW_HEIGHT_OF_HEADER
    }
    
    func tableView(_ tableView: UITableView, viewForHeaderInSection section: Int) -> UIView? {
        let width = UIScreen.main.bounds.width
        let padding:CGFloat = 8
        let widthOfAllElements = width - padding * 2
        
        let header = UIView(frame:CGRect(x: 0, y: 0, width: width, height: MOVE_CELL_VIEW_HEIGHT_OF_ROW))
        header.backgroundColor = UIColor(red: 79.0/255.0, green: 79.0/255.0, blue: 79.0/255.0, alpha: 1.0)
        
        let nameOfMoveLabel = UILabel(frame:CGRect(x: padding, y: 0, width: widthOfAllElements/3*2, height: MOVE_CELL_VIEW_HEIGHT_OF_HEADER))
        header.addSubview(nameOfMoveLabel)
        nameOfMoveLabel.text = "动作"
        nameOfMoveLabel.textColor = UIColor.white
        nameOfMoveLabel.font = UIFont.systemFont(ofSize: 12)
        
        let nameOfWeightLabel = UILabel(frame:CGRect(x: width/3*2, y: 0, width: widthOfAllElements/6, height: MOVE_CELL_VIEW_HEIGHT_OF_HEADER))
        header.addSubview(nameOfWeightLabel)
        nameOfWeightLabel.text = "负重(kg)"
        nameOfWeightLabel.textColor = UIColor.white
        nameOfWeightLabel.font = UIFont.systemFont(ofSize: 12)
        nameOfWeightLabel.textAlignment = .left
        
        let nameOfTimesLabel = UILabel(frame:CGRect(x: width-padding-widthOfAllElements/6, y: 0, width: widthOfAllElements/6, height: MOVE_CELL_VIEW_HEIGHT_OF_HEADER))
        header.addSubview(nameOfTimesLabel)
        nameOfTimesLabel.text = "强度(次)"
        nameOfTimesLabel.textColor = UIColor.white
        nameOfTimesLabel.font = UIFont.systemFont(ofSize: 12)
        nameOfTimesLabel.textAlignment = .right
        
        return header
    }
    
    func tableView(_ tableView: UITableView, cellForRowAt indexPath: IndexPath) -> UITableViewCell {
        let indexOfCell = indexPath.row
        let move = self.training.moves[indexOfCell]
        
        let moveCell:MoveCellView
        if let cell = tableView.dequeueReusableCell(withIdentifier: MOVE_CELL_VIEW_ID) as? MoveCellView {
            moveCell = cell
        } else {
            moveCell = MoveCellView(style: UITableViewCell.CellStyle.default, reuseIdentifier: MOVE_CELL_VIEW_ID)
        }
        
        moveCell.indexOfMove = indexOfCell
        moveCell.delegate = self
        moveCell.setMove(move: move)
        return moveCell
    }
    
    func tableView(_ tableView: UITableView, canEditRowAt indexPath: IndexPath) -> Bool {
        return true
    }
    
    func tableView(_ tableView: UITableView, commit editingStyle: UITableViewCell.EditingStyle, forRowAt indexPath: IndexPath) {
        if editingStyle == UITableViewCell.EditingStyle.delete {
            self.training.moves.remove(at: indexPath.row)
            self.movesTableView.reloadData()
        }
    }
    
    // MARK: - KeyboardToolbarDelegate
    func keyboardToolbarYesPressed(toolbar: WLKeyboardToolbar) {
        self.stopTextEdit()
    }
    
    // MARK: - MoveCellViewDelegate
    func editNameOfMoveBy(indexOfMove: Int) {
        if let vc = self.storyboard?.instantiateViewController(withIdentifier: "movepickervc") as? MovePickerViewController {
            vc.delegate = self
            
            self.present(vc, animated: true, completion: {
                vc.setSelected(nameOfMove: self.training.moves[indexOfMove].name, indexOfMoveInTraining: indexOfMove)
            })
        }
    }
    
    func afterMoveCellViewChanged(indexOfMove: Int, currentWeightOfMove: Int, currentTimesOfMove: Int) {
        self.training.moves[indexOfMove].weight = currentWeightOfMove
        self.training.moves[indexOfMove].times = currentTimesOfMove
        
        self.movesTableView.reloadData()
    }
    
    // MARK: - MovePickerViewControllerDelegate
    func movePickerViewControllerAfterSelect(move: String, indexOfMoveInTraining: Int) {
        self.training.moves[indexOfMoveInTraining].name = move
        
        self.movesTableView.reloadData()
    }
    
    
    // MARK: - GlassViewDelegate
    func glassViewTouchInsideUp() {
        self.stopTextEdit()
    }
    
    // MARK: - Private Methods
    fileprivate func setup() {
        self.movesTableView.delegate = self
        self.movesTableView.dataSource = self
        
        self.toolbar4Keyboard = WLKeyboardToolbar(delegate: self)
        self.view.addSubview(self.toolbar4Keyboard)
        
        self.glass4Keyboard = GlassView(frame: CGRect.zero)
        self.view.addSubview(self.glass4Keyboard)
        self.glass4Keyboard.delegate = self
        
        self.feelingTextView.delegate = self
    }
    
    fileprivate func populateTraining(selectedIndex:Int) {
        self.dateButton.setTitle(self.training.date.description, for: UIControl.State.normal)
        self.feelingTextView.text = self.training.feeling
        
        self.movesTableView.reloadData()
        if selectedIndex >= 0 && selectedIndex < self.training.moves.count {
            self.movesTableView.selectRow(at: IndexPath(row: selectedIndex, section: 0), animated: true, scrollPosition: UITableView.ScrollPosition.middle)
        }
    }
    
    fileprivate func stopTextEdit() {
        UIResponder.resignFirstResponder()
        self.toolbar4Keyboard.hide()
        self.glass4Keyboard.frame = CGRect.zero
    }
}

fileprivate class GlassView : UIView {
    fileprivate var delegate:GlassViewDelegate!
    
    override init(frame: CGRect) {
        super.init(frame: frame)
        
        self.backgroundColor = UIColor.clear
    }
    
    required init?(coder aDecoder: NSCoder) {
        fatalError("init(coder:) has not been implemented")
    }
    
    override func touchesEnded(_ touches: Set<UITouch>, with event: UIEvent?) {
        self.delegate.glassViewTouchInsideUp()
    }
}

protocol GlassViewDelegate {
    func glassViewTouchInsideUp()
}

/*
fileprivate class SimpleDatePickerEditor : UIControl, KeyboardToolbarDelegate {
    fileprivate var datePicker:UIDatePicker!
    fileprivate var toolbar:KeyboardToolbar!
    fileprivate var delegate:DatePickerEditorDelegate!
    
    fileprivate let initDate:SimpleDate
    
    init(frame: CGRect, initDate:SimpleDate) {
        self.initDate = initDate
        super.init(frame: frame)
        
        self.backgroundColor = UIColor(red: 0.0/255.0, green: 0.0/255.0, blue: 0.0/255.0, alpha: 0.5)
        
        let height_of_date_picker:CGFloat = 200
        self.toolbar = KeyboardToolbar(delegate: self)
        self.addSubview(self.toolbar)
        self.toolbar.moveTo(yPoint: UIScreen.main.bounds.height - height_of_date_picker - KeyboardToolbar.HEIGHT_OF_KEYBOARD_TOOLBAR)
        
        self.datePicker = UIDatePicker(frame: CGRect(x: 0, y: UIScreen.main.bounds.height - height_of_date_picker, width: UIScreen.main.bounds.width, height: height_of_date_picker))
        self.addSubview(self.datePicker)
        self.datePicker.backgroundColor = UIColor.white
        self.datePicker.datePickerMode = UIDatePickerMode.date
        self.datePicker.addTarget(self, action: #selector(onDatePickerValueChanged(_:)), for: UIControlEvents.valueChanged)
        self.datePicker.locale = Locale.current
        self.datePicker.date = self.initDate.asDate()
    }
    
    required init?(coder aDecoder: NSCoder) {
        fatalError("init(coder:) has not been implemented")
    }
    
    // MARK: - KeyboardToolbarDelegate
    func onKeyboardToolbarYesPressed(toolbar: KeyboardToolbar) {
        self.delegate.datePickerYesPressed(editor: self)
    }
    
    // MARK: - PrivateMethods
    @objc func onDatePickerValueChanged(_ dp:UIDatePicker) {
        let selectedDate = SimpleDate(date: dp.date)
        
        if selectedDate == self.initDate {
            self.toolbar.setYesButtonEnabled(enabled: true)
        } else if let _ = GCenter.getTrainingBy(date: selectedDate) {
            self.toolbar.setYesButtonEnabled(enabled: false)
        } else {
            self.toolbar.setYesButtonEnabled(enabled: true)
        }
    }
}

fileprivate protocol DatePickerEditorDelegate {
    func datePickerYesPressed(editor:SimpleDatePickerEditor)
}
 */

protocol DetailViewControllerDelegate {
    func onSaveDetailViewController(newTraining:GTraining)
}

fileprivate let MOVE_CELL_VIEW_ID = "MOVE_CELL_VIEW_ID_FOR_REUSE"
fileprivate let MOVE_CELL_VIEW_HEIGHT_OF_ROW:CGFloat = 44
fileprivate let MOVE_CELL_VIEW_HEIGHT_OF_HEADER:CGFloat = 34

class MoveCellView : UITableViewCell {
    fileprivate var moveButton:UIButton!
    fileprivate var weightTextField:UITextField!
    fileprivate var timesEachGroupTextField:UITextField!
    
    fileprivate var indexOfMove:Int!
    fileprivate var delegate:MoveCellViewDelegate!
    
    override init(style: UITableViewCell.CellStyle, reuseIdentifier: String?) {
        super.init(style: style, reuseIdentifier: reuseIdentifier)
        
        self.backgroundColor = UIColor.clear
        
        let width = UIScreen.main.bounds.width
        let padding:CGFloat = 8
        let widthOfAllElements = width - padding * 2
        
        self.moveButton = UIButton(frame:CGRect(x: padding, y: 0, width: widthOfAllElements/3*2, height: MOVE_CELL_VIEW_HEIGHT_OF_ROW))
        self.contentView.addSubview(self.moveButton)
        self.moveButton.setTitleColor(UIColor.red, for: UIControl.State.normal)
        self.moveButton.contentHorizontalAlignment = .left
        self.moveButton.addTarget(self, action: #selector(onMoveButtonClicked), for: UIControl.Event.touchUpInside)
        
        self.weightTextField = UITextField(frame:CGRect(x: width/3*2, y: 0, width: widthOfAllElements/6, height: MOVE_CELL_VIEW_HEIGHT_OF_ROW))
        self.contentView.addSubview(self.weightTextField)
        self.weightTextField.textAlignment = .left
        self.weightTextField.keyboardType = .numberPad
        self.weightTextField.addTarget(self, action: #selector(onMoveCellChanged), for: UIControl.Event.editingDidEnd)
        
        self.timesEachGroupTextField = UITextField(frame:CGRect(x: width-padding-widthOfAllElements/6, y: 0, width: widthOfAllElements/6, height: MOVE_CELL_VIEW_HEIGHT_OF_ROW))
        self.contentView.addSubview(self.timesEachGroupTextField)
        self.timesEachGroupTextField.textAlignment = .right
        self.timesEachGroupTextField.keyboardType = .numberPad
        self.timesEachGroupTextField.addTarget(self, action: #selector(onMoveCellChanged), for: UIControl.Event.editingDidEnd)
    }
    
    required init?(coder aDecoder: NSCoder) {
        fatalError("init(coder:) has not been implemented")
    }
    
    fileprivate func setMove(move:GMove) {
        self.moveButton.setTitle(move.name, for: UIControl.State.normal)
        self.weightTextField.text = String(move.weight)
        self.timesEachGroupTextField.text = String(move.times)
    }
    
    @objc func onMoveButtonClicked() {
        self.delegate.editNameOfMoveBy(indexOfMove: self.indexOfMove)
    }
    
    // MARK: - PrivateMethods
    @objc func onMoveCellChanged() {
        self.delegate.afterMoveCellViewChanged(indexOfMove:self.indexOfMove, currentWeightOfMove: Int(self.weightTextField.text!)!, currentTimesOfMove: Int(self.timesEachGroupTextField.text!)!)
    }
}

protocol MoveCellViewDelegate {
    func editNameOfMoveBy(indexOfMove:Int)
    
    func afterMoveCellViewChanged(indexOfMove:Int, currentWeightOfMove:Int, currentTimesOfMove:Int)
}
