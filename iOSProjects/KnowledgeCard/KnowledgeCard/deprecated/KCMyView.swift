//
//  MyView.swift
//  KnowledgeCard
//
//  Created by alex on 2018/6/5.
//  Copyright © 2018年 WhaleStudio. All rights reserved.
//

/*
import UIKit
import WhaleLib

private let PADDING_OF_IMAGE_BUTTON:CGFloat = 7
private let SIZE_OF_IMAGE_BUTTON:CGFloat = 30

private let TITLE_LAST_MODIFIED = "lastmodified"
private let TITLE_COUNT_OF_CARDS = "countofcards"
private let TITLE_COUNT_OF_IAMGE_CARDS = "countofimagecards"
private let TITLE_COUNT_OF_TEXT_CARDS = "countoftextcards"

class KCMyView : WLMyView, KCMainListener, UITableViewDelegate, UITableViewDataSource {
    private var closeButton:UIButton!
    
    private var lastModifiedLabel:UILabel!
    private var countOfCardsLabel:UILabel!
    private var countOfImageCardsLabel:UILabel!
    private var countOfTextCardsLabel:UILabel!
    
    private var informationTableView:UITableView!
    
    var delegate:KCMyViewDelegate!
    
    override init(frame: CGRect) {
        super.init(frame: frame)
        
        self.closeButton = UIButton()
        self.addSubview(self.closeButton)
        closeButton.snp.makeConstraints { (make) in
            make.left.equalTo(PADDING_OF_IMAGE_BUTTON)
            make.top.equalTo(PADDING_OF_IMAGE_BUTTON)
            make.width.height.equalTo(SIZE_OF_IMAGE_BUTTON)
        }
        closeButton.setImage(UIImage(named: "close_1024.png"), for: .normal)
        closeButton.addTarget(self, action: #selector(self.closeMyView), for: .touchUpInside)
    }
    
    required init?(coder aDecoder: NSCoder) {
        fatalError("init(coder:) has not been implemented")
    }
    
    override func safeAreaInsetsDidChange() {
        super.safeAreaInsetsDidChange()
        
        self.closeButton.snp.updateConstraints { (make) in
            make.top.equalTo(PADDING_OF_IMAGE_BUTTON + self.safeAreaInsets.top)
            make.left.equalTo(PADDING_OF_IMAGE_BUTTON + self.safeAreaInsets.left)
        }
    }
    
    // MARK: - Methods For Super Class
    override func abstractDecorateContentView(contentView: UIView) {
        super.abstractDecorateContentView(contentView: contentView)
        
        self.informationTableView = UITableView()
        self.informationTableView.delegate = self
        self.informationTableView.dataSource = self
        
        contentView.addSubview(self.informationTableView)
        self.informationTableView.snp.makeConstraints { (make) in
            make.center.equalTo(contentView)
            make.width.equalTo(contentView)
            make.height.equalTo(INFORMATION_TABLEVIEW_CELL_HEIGHT * CGFloat(informations.count))
        }
    }
    
    override func abstractDidLogout() {
        super.abstractDidLogout()
    }
    
    override func abstractDidLoginByEmailAndPasswordSuccessfully(passcode: String) {
        super.abstractDidLoginByEmailAndPasswordSuccessfully(passcode: passcode)
        
        KCMain.instance.sync()
    }
    
    // MARK: - KCMainListener
    func mainCardWillUpload2Server() {
        // do nothing
    }
    
    func mainCardDidUpload2Server(success: Bool) {
        // do nothing
    }
    
    func mainCardWillDownloadFromServer() {
        // do nothing
    }
    
    func mainCardsDownloadedFromServer(success: Bool) {
        // do nothing
    }
    
    func mainCardSynchronized() {
        // do nothing
    }
    
    func mainCardModified() {
        DispatchQueue.main.async {
            self.refreshInformation()
        }
    }
    
    // MARK: - UITableViewDelegate, UITabelViewDataSource
    func numberOfSections(in tableView: UITableView) -> Int {
        return 1
    }
    
    func tableView(_ tableView: UITableView, numberOfRowsInSection section: Int) -> Int {
        return informations.count
    }
    
    func tableView(_ tableView: UITableView, cellForRowAt indexPath: IndexPath) -> UITableViewCell {
        let theCell:UITableViewCell
        if let cell = tableView.dequeueReusableCell(withIdentifier: INFORMATION_TABLEVIEW_CELL_ID) {
            theCell = cell
        } else {
            theCell = UITableViewCell(style: .value1, reuseIdentifier: INFORMATION_TABLEVIEW_CELL_ID)
        }
        
        theCell.textLabel?.text = informations[indexPath.row].title()
        theCell.detailTextLabel?.text = informations[indexPath.row].valueText()
        
        return theCell
    }
    
    func tableView(_ tableView: UITableView, heightForRowAt indexPath: IndexPath) -> CGFloat {
        return INFORMATION_TABLEVIEW_CELL_HEIGHT
    }
    
    // MARK: - Instance Methods
    @objc private func closeMyView() {
        self.delegate.myViewClose()
    }
    
    private func refreshInformation() {
        self.informationTableView.reloadData()
    }
}

private let INFORMATION_TABLEVIEW_CELL_ID = "information_tableview_cell_id"
private let INFORMATION_TABLEVIEW_CELL_HEIGHT:CGFloat = 45

protocol KCMyViewDelegate {
    func myViewClose()
}

private let informations:[KCInfor] = [
    .lastmodified,
    .countofcards,
    .countofimagecards,
    .countoftextcards
]

private enum KCInfor {
    case lastmodified
    case countofcards
    case countofimagecards
    case countoftextcards
    
    func title() -> String {
        switch self {
        case .lastmodified:
            return "最近更新"
        case .countofcards:
            return "卡片"
        case .countofimagecards:
            return "图片"
        case .countoftextcards:
            return "文本"
        }
    }
    
    func valueText() -> String {
        switch self {
        case .lastmodified:
            let df = DateFormatter()
            df.locale = Locale.current
            df.dateFormat = "yyyy-MM-dd HH:mm:ss"
            return df.string(from: KCMain.instance.getLastModifiedOnline())
        case .countofcards:
            return String(KCMain.instance.count())
        case .countofimagecards:
            return String(KCMain.instance.countOfImageCard())
        case .countoftextcards:
            return String(KCMain.instance.countOfTextCard())
        }
    }
}
*/
