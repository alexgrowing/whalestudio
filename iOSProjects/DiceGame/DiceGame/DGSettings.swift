//
//  DGSettingsViewController.swift
//  DiceGame
//
//  Created by apple on 15/10/20.
//  Copyright © 2015年 WhaleStudio. All rights reserved.
//

import UIKit
import DiceGameLib
import WhaleLib
import SnapKit
import Photos
import MobileCoreServices

class DGSettingsViewController : UIViewController, UITableViewDataSource, UITableViewDelegate {
    fileprivate var informationTableView:UITableView!
    fileprivate var nickName:String!
    fileprivate var figureUrl:String!
    fileprivate var countOfCards:Int!
    fileprivate var countOfGold:Int!
    fileprivate var countOfCrown:Int!
    
    override func viewDidLoad() {
        let contentView = UIView()
        self.view.addSubview(contentView)
        contentView.snp.makeConstraints { (make) in
            make.edges.equalTo(self.view.safeAreaLayoutGuide.snp.edges)
        }
        
        let backButton = WLUI.createUIButton(titleOfButton: NSLocalizedString("OK", comment:""), target: self, action: #selector(DGSettingsViewController.back))
        contentView.addSubview(backButton)
        backButton.backgroundColor = UIColor.lightGray
        backButton.snp.makeConstraints { (make) in
            make.height.equalTo(DGUIUtils.HEIGHT_OF_NAVIGATION_BAR)
            make.left.equalTo(0)
            make.right.equalTo(0)
            make.bottom.equalTo(0)
        }
        
        self.informationTableView = UITableView()
        contentView.addSubview(informationTableView)
        self.informationTableView.snp.makeConstraints { (make) in
            make.left.equalTo(0)
            make.right.equalTo(0)
            make.top.equalTo(0)
            make.bottom.equalTo(backButton.snp.top)
        }
        self.informationTableView.tableFooterView = UIView(frame: CGRect.zero)
        self.informationTableView.dataSource = self
        self.informationTableView.delegate = self
        
        super.viewDidLoad()
        
        self.navigationItem.title = NSLocalizedString("My_Information", comment:"")
    }
    
    override func viewDidAppear(_ animated: Bool) {
        super.viewDidAppear(animated)
        
        self.refreshTableView()
    }
    
    // MARK: - UITableViewDataSource, UITableViewDelegate
    func numberOfSections(in tableView: UITableView) -> Int {
        return 2
    }
    
    func tableView(_ tableView: UITableView, numberOfRowsInSection section: Int) -> Int {
        if section == 0 {
            return 2
        } else {
            return 3
        }
    }
    
    func tableView(_ tableView: UITableView, cellForRowAt indexPath: IndexPath) -> UITableViewCell {
        let currentCell:UITableViewCell
        if let cell = tableView.dequeueReusableCell(withIdentifier: INFORMATION_TABLE_CELL_VIEW_ID) {
            currentCell = cell
        } else {
            currentCell = UITableViewCell(style: .value1, reuseIdentifier: INFORMATION_TABLE_CELL_VIEW_ID)
            currentCell.selectionStyle = .none
        }
        
        if indexPath.section == 0 {
            switch indexPath.row {
            case 0:
                currentCell.textLabel?.text = NSLocalizedString("Figure", comment:"")
                if self.figureUrl != nil {
                    let imageView = UIImageView(image: self.getFigureImage())
                    currentCell.contentView.addSubview(imageView)
                    imageView.snp.makeConstraints { (make) in
                        make.right.equalTo(0)
                        make.top.equalTo(0)
                        make.bottom.equalTo(0)
                        make.width.equalTo(currentCell.snp.height)
                    }
                }
                currentCell.accessoryType = .disclosureIndicator
            default:
                currentCell.textLabel?.text = NSLocalizedString("Nick_Name", comment:"")
                if self.nickName != nil {
                    currentCell.detailTextLabel?.text = self.nickName
                }
                currentCell.accessoryType = .disclosureIndicator
            }
        } else if indexPath.section == 1 {
            switch indexPath.row {
            case 0:
                currentCell.textLabel?.text = NSLocalizedString("Gold", comment:"")
                if self.countOfGold != nil {
                    currentCell.detailTextLabel?.text = String(describing: self.countOfGold!)
                }
            case 1:
                currentCell.textLabel?.text = NSLocalizedString("Crown", comment:"")
                if self.countOfGold != nil {
                    currentCell.detailTextLabel?.text = String(describing: self.countOfCrown!)
                }
            default:
                currentCell.textLabel?.text = NSLocalizedString("Lucky_Card", comment:"")
                if self.countOfCards != nil {
                    currentCell.detailTextLabel?.text = String(describing: self.countOfCards!)
                }
            }
        }
        
        return currentCell
    }
    
    func tableView(_ tableView: UITableView, heightForRowAt indexPath: IndexPath) -> CGFloat {
        return 60
    }
    
    func tableView(_ tableView: UITableView, didSelectRowAt indexPath: IndexPath) {
        if indexPath.section == 0 {
            switch indexPath.row {
            case 0:
                self.modifyFigure()
            case 1:
                self.modifyNickname()
            default:
                break
            }
        }
    }
    
    // MARK: - Instance Method
    @objc func back() {
        self.dismiss(animated: true, completion: nil)
    }
    
    private func modifyFigure() {
        let figureViewController = DGFigureViewController()
        self.navigationController?.pushViewController(figureViewController, animated: true)
    }
    
    fileprivate func getFigureImage() -> UIImage {
        return DGFigure(isURL: true, path: self.figureUrl).asImage()
    }
    
    private func modifyNickname() {
        let alertController = UIAlertController(title: title, message: NSLocalizedString("Nick_Name", comment:""), preferredStyle: UIAlertController.Style.alert)
        alertController.addTextField { (textField) -> Void in
            textField.text = self.nickName!
        }
        alertController.addAction(UIAlertAction(title: NSLocalizedString("Yes", comment:""), style: UIAlertAction.Style.default, handler: { (action) -> Void in
            if let newNameTF = alertController.textFields?.first {
                if let newName = newNameTF.text {
                    DGClientActions.myInformationChangeName(newName, {
                        self.refreshTableView()
                    })
                }
            }
        }))
        alertController.addAction(UIAlertAction(title:NSLocalizedString("Cancel", comment:""), style:UIAlertAction.Style.cancel, handler:nil))
        self.present(alertController, animated: true, completion: nil)
    }
    
    private func refreshTableView() {
        DGClientActions.myInformationView { (name, figure, countOfGold, countOfCards, countOfCrown) in
            self.nickName = name
            self.figureUrl = figure
            self.countOfGold = countOfGold
            self.countOfCards = countOfCards
            self.countOfCrown = countOfCrown
            
            DispatchQueue.main.async {
                self.informationTableView.reloadData()
            }
        }
    }
}

private let INFORMATION_TABLE_CELL_VIEW_ID = "INFORMATION_TABLE_CELL_VIEW_ID"

fileprivate class DGFigureViewController : UIViewController, UIImagePickerControllerDelegate, UINavigationControllerDelegate {
    private var bigFigureImageView:UIImageView!
    
    override func viewDidLoad() {
        let contentView = UIView()
        self.view.addSubview(contentView)
        contentView.snp.makeConstraints { (make) in
            make.edges.equalTo(self.view.safeAreaLayoutGuide.snp.edges)
        }
        
        self.bigFigureImageView = UIImageView()
        contentView.addSubview(self.bigFigureImageView)
        self.bigFigureImageView.snp.makeConstraints { (make) in
            make.width.height.equalTo(contentView.snp.width)
            make.top.equalTo(0)
        }
        
        let actionView = UIView()
        contentView.addSubview(actionView)
        actionView.snp.makeConstraints { (make) in
            make.top.equalTo(self.bigFigureImageView.snp.bottom)
            make.left.right.bottom.equalTo(0)
        }
        
        let widthOfButton:CGFloat = 180
        let heightOfButton:CGFloat = 60
        
        let choosePhotoButton = DGUIUtils.createHomeButton(name: NSLocalizedString("Choose_From_Album", comment:""), target: self, action: #selector(DGFigureViewController.chooseAPhotoFromAlbum))
        actionView.addSubview(choosePhotoButton)
        choosePhotoButton.snp.makeConstraints { (make) in
            make.bottom.equalTo(actionView.snp.centerY).offset(-20)
            make.centerX.equalTo(actionView.snp.centerX)
            make.width.equalTo(widthOfButton)
            make.height.equalTo(heightOfButton)
        }
        
        let takePhotoButton = DGUIUtils.createHomeButton(name: NSLocalizedString("Take_A_Photo", comment:""), target: self, action: #selector(DGFigureViewController.takeAPhoto))
        actionView.addSubview(takePhotoButton)
        takePhotoButton.snp.makeConstraints { (make) in
            make.top.equalTo(actionView.snp.centerY).offset(20)
            make.centerX.equalTo(actionView.snp.centerX)
            make.width.equalTo(widthOfButton)
            make.height.equalTo(heightOfButton)
        }
        
        super.viewDidLoad()
        
        self.navigationItem.title = NSLocalizedString("My_Figure", comment:"")
    }
    
    override func viewWillAppear(_ animated: Bool) {
        super.viewWillAppear(animated)
        
        self.refreshFigureImage()
    }
    
    // MARK: - UINavigationControllerDelegate
    // MARK: - UIImagePickerControllerDelegate
    func imagePickerController(_ picker: UIImagePickerController, didFinishPickingMediaWithInfo info: [UIImagePickerController.InfoKey : Any]) {
        // Local variable inserted by Swift 4.2 migrator.
        let info = convertFromUIImagePickerControllerInfoKeyDictionary(info)
        
        self.dismiss(animated: true) {
            if let image = info[convertFromUIImagePickerControllerInfoKey(UIImagePickerController.InfoKey.editedImage)] as? UIImage {
                let minSize = min(image.size.width, image.size.height)
                let rect:CGRect
                
                switch image.imageOrientation {
                case .up, .upMirrored, .down, .downMirrored:
                    if minSize == image.size.width {
                        rect = CGRect(x: (image.size.height - minSize) / 2, y: 0, width: minSize, height: minSize)
                    } else {
                        rect = CGRect(x: 0, y: (image.size.width - minSize) / 2, width: minSize, height: minSize)
                    }
                default:
                    if minSize == image.size.width {
                        rect = CGRect(x: 0, y: (image.size.height - minSize) / 2, width: minSize, height: minSize)
                    } else {
                        rect = CGRect(x: (image.size.width - minSize) / 2, y: 0, width: minSize, height: minSize)
                    }
                }
                
                let clippedImage = WLUI.clipImage(image, rect: rect)
                let image2Upload = WLUI.resize(sourceImage: clippedImage!, sizeOfLongSide: UIScreen.main.bounds.width)
                
//                UIImageWriteToSavedPhotosAlbum(image2Upload, self, nil, nil)
                
                WLAccount.uploadFigure(image: image2Upload, callback: { (success) in
                    if success {
                        DispatchQueue.main.async {
                            self.refreshFigureImage()
                        }
                    }
                })
            }
        }
    }
    
    func imagePickerControllerDidCancel(_ picker: UIImagePickerController) {
        self.dismiss(animated: true) {
        }
    }
    
    func refreshFigureImage() {
        if let theSettingsVC = self.navigationController?.viewControllers[0] as? DGSettingsViewController {
            self.bigFigureImageView.image = theSettingsVC.getFigureImage()
        }
    }
    
    @objc func chooseAPhotoFromAlbum() {
        let authorization = PHPhotoLibrary.authorizationStatus()
        
        self.checkPhotoAuthroization(status: authorization, authorizedCallback: {
            self.showImagePicker()
        })
    }
    
    @objc func takeAPhoto() {
        let authorization = AVCaptureDevice.authorizationStatus(for: .video)
        
        self.checkCameraAuthorization(status: authorization) {
            self.showCameraPicker()
        }
    }
    
    private func checkCameraAuthorization(status:AVAuthorizationStatus, authorizedCallback:@escaping ()->Void) {
        switch status {
        case .notDetermined:
            print("video:notDetermined")
            AVCaptureDevice.requestAccess(for: .video) { (granted) in
                if granted {
                    authorizedCallback()
                } else {
                    self.checkCameraAuthorization(status: .denied, authorizedCallback: authorizedCallback)
                }
            }
        case .restricted:
            print("video:restricted")
        case .denied:
            print("video:denied")
            self.ask4OpenSettings(message: NSLocalizedString("Camera_Authorization_Is_Needed", comment: ""))
        case .authorized:
            print("video:authorized")
            authorizedCallback()
            
        default:
            break
        }
    }
    
    private func showCameraPicker() {
        let imagePickerVC = UIImagePickerController()
        imagePickerVC.allowsEditing = true
        imagePickerVC.sourceType = .camera
        imagePickerVC.mediaTypes = [kUTTypeImage as String]
        imagePickerVC.videoQuality = .typeMedium
        imagePickerVC.delegate = self
        
        self.present(imagePickerVC, animated: true) {
            // do nothing
        }
    }
    
    private func checkPhotoAuthroization(status:PHAuthorizationStatus, authorizedCallback:@escaping ()->Void) {
        switch status {
        case .notDetermined:
            print("notDetermined")
            PHPhotoLibrary.requestAuthorization { (status) in
                self.checkPhotoAuthroization(status: status, authorizedCallback: authorizedCallback)
            }
        case .restricted:
            print("restricted")
        case .denied:
            print("denied")
            self.ask4OpenSettings(message: NSLocalizedString("Photo_Authorization_Is_Needed", comment: ""))
        case .authorized:
            print("authorized")
            authorizedCallback()
        default:
            break
        }
    }
    
    private func showImagePicker() {
        let imagePickerVC = UIImagePickerController()
        imagePickerVC.allowsEditing = true
        imagePickerVC.sourceType = .photoLibrary
        imagePickerVC.mediaTypes = [kUTTypeImage as String]
        imagePickerVC.delegate = self
        
        self.present(imagePickerVC, animated: true) {
            // do nothing
        }
    }
    
    private func ask4OpenSettings(message:String) {
        let vc = WLUI.alertAsk(title: NSLocalizedString("Go_To_Settings", comment: ""), message: message) {
            if let url = URL(string: UIApplication.openSettingsURLString) {
                if UIApplication.shared.canOpenURL(url) {
                    UIApplication.shared.open(url, options: [:]) { (success) in
                        // do nothing
                    }
                }
            }
        }
        
        self.present(vc, animated: true) {
            // do nothing
        }
    }
}

// Helper function inserted by Swift 4.2 migrator.
fileprivate func convertFromUIImagePickerControllerInfoKeyDictionary(_ input: [UIImagePickerController.InfoKey: Any]) -> [String: Any] {
    return Dictionary(uniqueKeysWithValues: input.map {key, value in (key.rawValue, value)})
}

// Helper function inserted by Swift 4.2 migrator.
fileprivate func convertFromUIImagePickerControllerInfoKey(_ input: UIImagePickerController.InfoKey) -> String {
    return input.rawValue
}
