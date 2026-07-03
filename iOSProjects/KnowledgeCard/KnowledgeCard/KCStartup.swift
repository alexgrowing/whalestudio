//
//  KCStartup.swift
//  KnowledgeCard
//
//  Created by alex on 2018/4/28.
//  Copyright © 2018年 WhaleStudio. All rights reserved.
//

import UIKit
import SnapKit
import MobileCoreServices
import Photos
import AVFoundation
import WhaleLib

class KCStartupViewController : UIViewController, KCEditViewControllerDelegate, UIImagePickerControllerDelegate, UINavigationControllerDelegate, KCMainListener, KCThumbnailCollectionViewDelegate, KCDataSource, KCShuffleViewControllerDelegate {
    public static let NOTIFICATION_PASTE = "NOTIFICATION_PASTE"
    
    @IBOutlet weak var stateOfSyncButton: UIButton!
    @IBOutlet weak var searchContentTextField: UITextField!
    @IBOutlet weak var searchButton: UIButton!
    @IBOutlet weak var glassView4Search: UIView!
    @IBOutlet weak var reloadIndicator: UIActivityIndicatorView!
    
    @IBOutlet weak var thumbCollectionView: KCThumbnailCollectionView!
    private var shuffleViewController:KCShuffleViewController!
    
    private var keyword2Search:String!
    private var collection:KCKnowledgeCollection!
    
    override func viewDidLoad() {
        super.viewDidLoad()
        
        self.setStateOfSync(.LostConnection)
        
        self.thumbCollectionView.thumbnailDelegate = self
        self.thumbCollectionView.thumbnailDataSource = self
        
        WLAccount.authenticateLocalUserByGameCenter { (auth) in
            switch auth {
            case .did_login_by_gamecenter:
                self.didLogin()
                break
            case let .should_popup_gamecenter_login_first(loginViewController):
                self.present(loginViewController, animated: true, completion: {
                    // do nothing
                })
            case .should_login_ignore_gamecenter:
                print("should login ignore game center")
                
                break
            }
        }
    }
    
    private func didLogin() {
        KCMain.instance.append(listener: self)
        KCMain.instance.sync()
        
        self.reloadIndicator.isHidden = true
        self.setStateOfSync(.Sync)
        
        NotificationCenter.default.addObserver(self, selector: #selector(self.checkContentFromPaste), name: NSNotification.Name(rawValue: KCStartupViewController.NOTIFICATION_PASTE), object: nil)
        
        DispatchQueue.main.asyncAfter(deadline: DispatchTime.now() + Double(Int64(1 * NSEC_PER_SEC)) / Double(NSEC_PER_SEC)) {
            self.checkContentFromPaste()
        }
    }
    
    // MARK: - KCMainListener
    func mainCardWillDownloadFromServer() {
        DispatchQueue.main.async {
            self.setStateOfSync(.Download)
        }
    }
    
    func mainCardsDownloadedFromServer(success:Bool) {
        DispatchQueue.main.async {
            if success {
                self.setStateOfSync(.Sync)
            } else {
                self.setStateOfSync(.LostConnection)
            }
        }
    }
    
    func mainCardWillUpload2Server() {
        DispatchQueue.main.async {
            self.setStateOfSync(.Upload)
        }
    }
    
    func mainCardDidUpload2Server(success: Bool) {
        DispatchQueue.main.async {
            if success {
                self.setStateOfSync(.Sync)
            } else {
                self.setStateOfSync(.LostConnection)
            }
        }
    }
    
    func mainCardSynchronized() {
        DispatchQueue.main.async {
            self.setStateOfSync(.Sync)
        }
    }
    
    func mainCardModified() {
        // do nothing
    }
    
    // MARK: - KCThumbnailCollectionViewDelegate
    func thumbnailCollectionViewDidSelect(indexOfThumbs: Int) {
        self.presentShuffleView(from:indexOfThumbs, order:true)
    }
    
    // MARK: - KCDataSource
    func datasourceCountOfThumbs() -> Int {
        if let theCollection = self.collection {
            return theCollection.count()
        } else {
            return 0
        }
    }
    
    func datasourceKnowledgeBy(index: Int) -> KCKnowledge {
        return self.collection.knowledgeBy(index:index)
    }
    
    func datasourceDeleteKnowledgeBy(index: Int) {
        self.collection.deleteKnowledgeBy(index: index)
    }
    
    // MARK: - KCShuffleViewControllerDelegate
    func kcShuffleDidExit() {
        self.refreshThumbnailsByCleanKeywords()
    }
    
    // MARK: - IBActions
    @IBAction func btnSearchButtonClicked() {
        if !self.searchContentTextField.isEnabled {
            self.searchContentTextField.isEnabled = true
            self.searchContentTextField.becomeFirstResponder()
            self.searchButton.setImage(UIImage(named: "close_1024.png"), for: .normal)
        } else {
            self.searchContentTextField.resignFirstResponder()
            self.searchContentTextField.isEnabled = false
            self.searchButton.setImage(UIImage(named: "search_1024.png"), for: .normal)
        }
    }
    
    @IBAction func createNewTextCard(_ sender: UIBarButtonItem) {
        self.createNewCardWith(text: "")
    }
    @IBAction func createNewImageCard(_ sender: Any) {
        let authorization = PHPhotoLibrary.authorizationStatus()
        
        self.checkPhotoAuthroization(status: authorization, authorizedCallback: {
            self.showImagePicker()
        })
    }
    @IBAction func tfSearchContentChanged() {
        guard let keyword = self.searchContentTextField.text else {
            return
        }
        
        if let theKeyword2Search = self.keyword2Search, theKeyword2Search == keyword {
            return
        }
        
        self.keyword2Search = keyword
        self.reloadIndicator.isHidden = false
        
        DispatchQueue.main.asyncAfter(deadline: DispatchTime.now() + Double(Int64(2 * NSEC_PER_SEC)) / Double(NSEC_PER_SEC)) {
            if keyword == self.searchContentTextField.text! {
                self.collection = KCMain.instance.knowledgesBy(keyword: keyword)
                self.thumbCollectionView.reloadData()
                self.reloadIndicator.isHidden = true
                self.keyword2Search = nil
            }
        }
    }
    @IBAction func tfSearchDidStart() {
        self.glassView4Search.isHidden = false
    }
    @IBAction func tfSearchDidEnd() {
        self.glassView4Search.isHidden = true
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
            self.ask4OpenSettings(message: "需要打开照片权限")
        case .authorized:
            print("authorized")
            authorizedCallback()
        }
    }
    
    private func showImagePicker() {
        let imagePickerVC = UIImagePickerController()
        imagePickerVC.allowsEditing = false
        imagePickerVC.sourceType = .photoLibrary
        imagePickerVC.mediaTypes = [kUTTypeImage as String]
        imagePickerVC.delegate = self
        
        self.present(imagePickerVC, animated: true) {
            // do nothing
        }
    }
    
    @IBAction func createNewPhotoCard(_ sender: Any) {
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
            self.ask4OpenSettings(message: "需要打开相机权限")
        case .authorized:
            print("video:authorized")
            authorizedCallback()
        }
    }
    
    private func showCameraPicker() {
        let imagePickerVC = UIImagePickerController()
        imagePickerVC.allowsEditing = false
        imagePickerVC.sourceType = .camera
        imagePickerVC.mediaTypes = [kUTTypeImage as String]
        imagePickerVC.videoQuality = .typeMedium
        imagePickerVC.delegate = self
        
        self.present(imagePickerVC, animated: true) {
            // do nothing
        }
    }
    
    private func ask4OpenSettings(message:String) {
        let vc = WLUI.alertAsk(title: "跳转设置", message: message) {
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
    
    @IBAction func btnGotoShuffleMode(_ sender: Any) {
        if KCMain.instance.count() == 0 {
            let alert = WLUI.alert(title: "卡片为空", message: nil)
            self.present(alert, animated: true, completion: nil)
        } else {
            self.presentShuffleView(from:KCMain.instance.count() - 1, order:false)
        }
    }
    
    // MARK: - UIImagePickerControllerDelegate
    func imagePickerController(_ picker: UIImagePickerController, didFinishPickingMediaWithInfo info: [UIImagePickerController.InfoKey : Any]) {
// Local variable inserted by Swift 4.2 migrator.
let info = convertFromUIImagePickerControllerInfoKeyDictionary(info)

        self.dismiss(animated: true) {
            if let image = info[convertFromUIImagePickerControllerInfoKey(UIImagePickerController.InfoKey.originalImage)] as? UIImage {
                self.createNewCardWith(image: image)
            }
        }
    }
    
    func imagePickerControllerDidCancel(_ picker: UIImagePickerController) {
        self.dismiss(animated: true) {
        }
    }
    
    // MARK: - UINavigationControllerDelegate
    
    // MARK: - KCEditViewControllerDelegate
    func kcEditViewControllerAfterEdit(uuid: String) {
        self.refreshThumbnailsByCleanKeywords()
    }
    
    // MARK: - Instance Methods
    private func createNewCardWith(text:String) {
        let kl = KCMain.instance.appendKnowledgeOf(text: text)
        
        self.didCreateNewCardWith(kl: kl)
        
        if text.count == 0 {
            self.edit(textKnowledge:kl)
        }
    }
    
    private func createNewCardWith(image:UIImage) {
        let kl = KCMain.instance.appendKnowledgeOf(image: image)
        
        self.didCreateNewCardWith(kl: kl)
    }
    
    private func didCreateNewCardWith(kl:KCKnowledge) {
        self.refreshThumbnailsByCleanKeywords()
    }
    
    private func edit(textKnowledge:KCTextKnowledge) {
        if let vc = self.storyboard?.instantiateViewController(withIdentifier: "editvc") as? KCEditViewController {
            
            self.present(vc, animated: true) {
                vc.set(textKL: textKnowledge, delegate: self)
            }
        }
    }
    
    @objc private func checkContentFromPaste() {
        if !self.isViewLoaded || self.view.window == nil {
            return
        }
        
        if let paste = UIPasteboard.general.string {
            if paste == KCMain.instance.lastCheckedMessageFromPaste {
                return
            }
            
            if paste.trimmingCharacters(in: .whitespacesAndNewlines).count == 0 {
                return
            }
            
            KCMain.instance.lastCheckedMessageFromPaste = paste
            
            var message = paste
            if message.count > 50 {
                message = String(message.prefix(50)) + "..."
            }
            let alert = UIAlertController(title: nil, message: message, preferredStyle: UIAlertController.Style.alert)
            alert.addAction(UIAlertAction(title: "新建", style: UIAlertAction.Style.default, handler: { (action) in
                self.createNewCardWith(text: paste)
            }))
            alert.addAction(UIAlertAction(title: "忽略", style: UIAlertAction.Style.cancel, handler: nil))
            
            self.present(alert, animated: true, completion: {
                // do nothing
            })
            
        }
    }
    
    private func animateUpdateConstraints() {
        self.view.setNeedsUpdateConstraints()
        
        UIView.animate(withDuration: 0.5) {
            self.view.layoutIfNeeded()
        }
    }
    
    private func setStateOfSync(_ state:StateOfSync) {
        let newImageName:String
        switch state {
        case .LostConnection:
            newImageName = "lost_connect_1024.png"
        case .Sync:
            newImageName = "sync_1024.png"
            self.refreshThumbnailsByCleanKeywords()
            
        case .Upload:
            newImageName = "upload_1024.png"
        case .Download:
            newImageName = "download_1024.png"
        }
        
        self.stateOfSyncButton.setImage(UIImage(named: newImageName), for: .normal)
    }
    
    private func refreshThumbnailsByCleanKeywords() {
        self.collection = KCMain.instance.knowledgesBy(keyword: nil)

        self.thumbCollectionView.reloadData()
    }
    
    private func presentShuffleView(from:Int, order:Bool) {
        if self.shuffleViewController == nil {
            self.shuffleViewController = (self.storyboard?.instantiateViewController(withIdentifier: "shuffle")) as? KCShuffleViewController
            self.shuffleViewController.shuffleDataSource = self
            self.shuffleViewController.shuffleDelegate = self
        }
        
        self.present(self.shuffleViewController, animated: true) {
            self.shuffleViewController.resetOrdersBy(startIndex: from, order: order)
        }
    }
    
    /*
    private func printInfo() {
        print("***************************************")
        print("nextKL2LoadInOrders:\(self.nextKL2LoadInOrders)")
        print("indexInOrdersOfCardShowing:\(self.indexInOrdersOfCardShowing)")
        print("orders:\(self.orders)")
        for view in self.loadedCardViews {
            if let tv = view as? UITextView {
                print("content:\(tv.text)")
            }
        }
    }
 */
}

private enum StateOfSync {
    case LostConnection
    case Sync
    case Upload
    case Download
}

protocol KCDataSource {
    func datasourceCountOfThumbs() -> Int
    func datasourceKnowledgeBy(index:Int) -> KCKnowledge
    func datasourceDeleteKnowledgeBy(index:Int)
}

// Helper function inserted by Swift 4.2 migrator.
fileprivate func convertFromUIImagePickerControllerInfoKeyDictionary(_ input: [UIImagePickerController.InfoKey: Any]) -> [String: Any] {
	return Dictionary(uniqueKeysWithValues: input.map {key, value in (key.rawValue, value)})
}

// Helper function inserted by Swift 4.2 migrator.
fileprivate func convertFromUIImagePickerControllerInfoKey(_ input: UIImagePickerController.InfoKey) -> String {
	return input.rawValue
}
