//
//  ViewController.swift
//  Land
//
//  Created by apple on 15/12/7.
//  Copyright © 2015年 G & B. All rights reserved.
//

import UIKit
import GameKit
import MapKit
import HealthKit
import GoogleMobileAds
import WhaleLib
import LandLib

private let DEFAULTS_FOOTPRINTS = "defaults_footprints"
private let DEFAULTS_LASTDATEANDSTEP = "defaults_last_date_and_step"

private let CURRENT_APP_DOWNLOAD_URL = "https://itunes.apple.com/us/app/qiang-pan-qiang-zhen-shi-shi/id1069771057"
private let REVIEW_APP_URL = "http://itunes.apple.com/WebObjects/MZStore.woa/wa/viewContentsUserReviews?id=1069771057&pageNumber=0&sortOrdering=2&type=Purple+Software&mt=8"

private let INAPP_PURCHASE_DIAMOND_50 = "diamond_50"

private let ANNOTATION_VISIBLE_LONGITUDE_SPAN = 0.03

class ViewController: UIViewController, MKMapViewDelegate, UIGestureRecognizerDelegate, GADBannerViewDelegate, GKGameCenterControllerDelegate, RLMyInformationViewControllerDelegate, RLTerritoryInforViewDelegate, RLAddSoldierViewDelegate, RLAddDiamondViewDelegate, RLCampaignViewDelegate, RLFightResultViewDelegate, RLGoverTerritoryViewDelegate, RLUpdateVersionViewDelegate, RLTrainingProgressViewDelegate, RLMyFightsViewDelegate,RLRequestHealthViewDelegate, SKProductsRequestDelegate, SKPaymentTransactionObserver {

    @IBOutlet weak var unmatchedAccountTipButton: UIButton!
    @IBOutlet weak var animationViewOnMapTapped: UIView!
    @IBOutlet weak var map: MKMapView! {
        didSet {
            map.mapType = .standard
            map.delegate = self
            map.showsUserLocation = true
            map.isPitchEnabled = false
            map.isRotateEnabled = false
        }
    }
    
    @IBOutlet weak var loadingView: UIView!
    @IBOutlet weak var loadingMessageLabel: UILabel!
    @IBOutlet weak var loadingProgressView: UIProgressView!
        
    @IBOutlet weak var updateLocationButton: UIButton!
    
    @IBOutlet weak var myNameButton: UIButton!
    @IBOutlet weak var checkTrainingProgressButton: UIButton!
    @IBOutlet weak var recruitSoldierButton: UIButton!
    @IBOutlet weak var countOfGoldLabel: UILabel!
    @IBOutlet weak var countOfSoldierLabel: UILabel!
    @IBOutlet weak var countOfDiamondLabel: UILabel!
    
    @IBOutlet weak var imageOfMyGoldResource: UIImageView!
    
    @IBOutlet weak var readStepButton: UIButton!
    @IBOutlet weak var imageOfCountOfNewFights: UIImageView!
    
    fileprivate var updateVersionView : RLUpdateVersionView!
    fileprivate var requestHealthView : RLRequestHealthView!
    fileprivate var territoryInforView: RLTerritoryInforView!
    fileprivate var addSoldierView : RLAddSoldierView!
    fileprivate var addDiamondView : RLAddDiamondView!
    fileprivate var campaignView : RLCampaignView!
    fileprivate var fightResultView : RLFightResultView!
    fileprivate var goverTerritoryView : RLGoverTerritoryView!
    fileprivate var trainingProgressView : RLTrainingProgressView!
    fileprivate var myFightsView : RLMyFightsView!
    
    fileprivate var healthKitStore:HKHealthStore!
    fileprivate var locationManager : CLLocationManager!
    
    fileprivate var mapOfTerritory2Renderer = [Territory:TerritoryRenderer]()
    fileprivate var mapOfTerritory2Annotation = [Territory:TerritoryAnnotation]()
    fileprivate var mapOfTerritory2Detail = [Territory:TerritoryInfo]()
    
    fileprivate var isAnnotationVisible:Bool = false {
        didSet {
            let territoriesInRegion:Set<Territory>
            if self.isAnnotationVisible {
                territoriesInRegion = calculateTerritoriesByRegion(self.map.region)
            } else {
                territoriesInRegion = Set<Territory>()
            }
            
            for (ter, _) in self.mapOfTerritory2Annotation {
                if !territoriesInRegion.contains(ter) {
                    self.removeTerritoryAnnotationFromMap(ter)
                }
            }
            
            guard let theUser = RLUser.getCurrentUser() else {return}
            for ter in territoriesInRegion {
                if !theUser.visitedTerritory(ter) {
                    continue
                }
                if self.mapOfTerritory2Annotation[ter] == nil {
                    self.addTerritoryAnnotation2Map(ter)
                }
            }
        }
    }
    fileprivate var myLastFootprint:MyFootprint?
    fileprivate var lastTerritoryIAmIn : Territory?
    fileprivate var driveModel = false {
        didSet {
            let image:String
            if self.driveModel {
                UIApplication.shared.isIdleTimerDisabled = true
                image = "locationon.png"
            } else {
                UIApplication.shared.isIdleTimerDisabled = false
                image = "locationaway.png"
            }
            
            self.updateLocationButton.setBackgroundImage(UIImage(named: image), for: UIControl.State())
        }
    }
    
    override var prefersStatusBarHidden : Bool {
        return true
    }
    
    override func viewDidLoad() {
        super.viewDidLoad()
        // Do any additional setup after loading the view, typically from a nib.
        
        switch CLLocationManager.authorizationStatus() {
        case .authorizedAlways:
            printLog("location authorized always")
        case .authorizedWhenInUse:
            printLog("location authorized in use")
        case .denied:
            printLog("location auth denied")
        case .notDetermined:
            printLog("location auth not determined")
        case .restricted:
            printLog("location auth restricted")
        }
        
        self.locationManager = CLLocationManager()
        self.locationManager.desiredAccuracy = kCLLocationAccuracyBest
        self.locationManager.requestWhenInUseAuthorization()
        
        self.loadCustomViews()
        self.registerGestureRecognizer()
        
        NotificationCenter.default.addObserver(self, selector: #selector(keyboardWillShow(_:)), name: UIResponder.keyboardWillShowNotification, object: nil)
        NotificationCenter.default.addObserver(self, selector: #selector(keyboardWillHide(_:)), name: UIResponder.keyboardWillHideNotification, object: nil)
        
        SKPaymentQueue.default().add(self)

        self.login()
    }

    override func didReceiveMemoryWarning() {
        super.didReceiveMemoryWarning()
        // Dispose of any resources that can be recreated.
    }
    
    // MARK: - MKMapViewDelegate
    func mapView(_ mapView: MKMapView, didFailToLocateUserWithError error: Error) {
        printLog(error.localizedDescription)
    }
    
    func mapViewWillStartLocatingUser(_ mapView: MKMapView) {
        printLog("开始定位")
    }
    
    func mapViewDidStopLocatingUser(_ mapView: MKMapView) {
        printLog("停止定位")
    }
    
    func mapView(_ mapView: MKMapView, regionDidChangeAnimated animated: Bool) {
        self.isAnnotationVisible = mapView.region.span.longitudeDelta < ANNOTATION_VISIBLE_LONGITUDE_SPAN
    }
    
    func mapView(_ mapView: MKMapView, didUpdate userLocation: MKUserLocation) {
        if self.myLastFootprint == nil || self.driveModel {
            self.gotoMyLocation()
        }
        
        self.myLastFootprint = MyFootprint(currentCoordinate: userLocation.coordinate, lastCoordinate: self.myLastFootprint?.coordinate)
        mapView.view(for: mapView.userLocation)?.setNeedsDisplay()
        
        self.try2AddNewFootprint(calculateTerritoryByLocation(userLocation.coordinate))
    }
    
    func mapView(_ mapView: MKMapView, viewFor annotation: MKAnnotation) -> MKAnnotationView? {
        // 加这一段的目的是为了把【将点击当前位置的小蓝点时会弹出Current Location】的问题搞定
        if let userLocationAnnotation = annotation as? MKUserLocation {
            userLocationAnnotation.title = ""
            return nil
/*
            let retView:RLUserAnnotationView
            if let pinView = mapView.dequeueReusableAnnotationViewWithIdentifier("UserLocation") as? RLUserAnnotationView {
                retView = pinView
            } else {
                retView = RLUserAnnotationView(annotation: userLocationAnnotation, reuseIdentifier: "UserLocation")
            }
            
            if let theLastFootprint = self.myLastFootprint {
                retView.setAngleOfFootprint(CGFloat(theLastFootprint.angle))
            }
            
            return retView
*/
        }
        
        if let theTerAnnotation = annotation as? TerritoryAnnotation {
            let identifier = "TerritoryAnnotation_\(theTerAnnotation.title!)"
            var pinView = mapView.dequeueReusableAnnotationView(withIdentifier: identifier)
            
            if pinView == nil {
                pinView = MKAnnotationView(annotation: theTerAnnotation, reuseIdentifier: identifier)
            } else {
                for subview in (pinView?.subviews)! {
                    subview.removeFromSuperview()
                }
            }
            
            let info = self.mapOfTerritory2Detail[theTerAnnotation.territory]
            if info == nil {
                self.refreshTerritoryDetailInfo(theTerAnnotation.territory, callback: { (detail) -> Void in
                    DispatchQueue.main.async(execute: {
                        self.decorateAnnotationView(pinView!, info:detail)
                    })
                })
            } else {
                self.decorateAnnotationView(pinView!, info:info!)
            }
            
            return pinView
        }
        
        /*
else if let theFootprintAnnotation = annotation as? MyFootprintAnnotation {
            var pinView = mapView.dequeueReusableAnnotationViewWithIdentifier("FootprintAnnotation")
            if pinView == nil {
                pinView = MKAnnotationView(annotation: theFootprintAnnotation, reuseIdentifier: "FootprintAnnotation")
            } else {
                for subview in (pinView?.subviews)! {
                    subview.removeFromSuperview()
                }
            }
            
            if mapView.region.span.longitudeDelta < 0.03 {
                let footprintImageView = UIImageView(frame:CGRectMake(0,0,10,10))
                footprintImageView.image = FOOTPRINT_OF_SIZE_9_IMAGE
                pinView!.addSubview(footprintImageView)
                footprintImageView.transform = CGAffineTransformMakeRotation(CGFloat(theFootprintAnnotation.angle))
            }
            
            return pinView
        }
*/
        
        return nil
    }
    
    func decorateAnnotationView(_ pinView:MKAnnotationView, info:TerritoryInfo) {
        let padding:CGFloat = 5
        let heightOfNameOfTerritoryLabel:CGFloat = 20
        let widthOfPinView:CGFloat = 130
        
        let nameOfTerritoryLabel = UILabel(frame:CGRect(x: padding,y: padding,width: widthOfPinView-padding*2,height: heightOfNameOfTerritoryLabel))
        pinView.addSubview(nameOfTerritoryLabel)
        nameOfTerritoryLabel.text = info.name
        nameOfTerritoryLabel.font = UIFont.boldSystemFont(ofSize: heightOfNameOfTerritoryLabel)
        nameOfTerritoryLabel.textColor = UIColor.white
        nameOfTerritoryLabel.adjustsFontSizeToFitWidth = true
        nameOfTerritoryLabel.textAlignment = .left
        
        if info.ownerName.count > 0 {
            let heightOfNameOfOwnerLabel:CGFloat = 10
            let nameOfOwnerLabel = UILabel(frame: CGRect(x: padding,y: padding*2+heightOfNameOfTerritoryLabel,width: widthOfPinView-padding*2,height: heightOfNameOfOwnerLabel))
            //        label.layer.cornerRadius = 5.0
            //        label.layer.masksToBounds = true
            //        label.layer.backgroundColor = UIColor.blueColor().CGColor
            //        label.layer.borderColor = UIColor.lightGrayColor().CGColor
            //        label.layer.borderWidth = 1.0
            
            nameOfOwnerLabel.textAlignment = .left
            nameOfOwnerLabel.font = UIFont.boldSystemFont(ofSize: heightOfNameOfOwnerLabel)
            nameOfOwnerLabel.text = info.ownerName
            nameOfOwnerLabel.textColor = UIColor.white
            nameOfOwnerLabel.adjustsFontSizeToFitWidth = true
            pinView.addSubview(nameOfOwnerLabel)
        }
        
        /*
        let image = UIImage(named: "logo.png")
        let imageView = UIImageView(image: image)
        imageView.layer.cornerRadius = 5.0
        imageView.layer.masksToBounds = true
        imageView.layer.borderColor = UIColor.lightGrayColor().CGColor
        imageView.layer.borderWidth = 1.0
        pinView?.addSubview(imageView)
        */
    }
    
    func mapView(_ mapView: MKMapView, rendererFor overlay: MKOverlay) -> MKOverlayRenderer {
        if let ter = overlay as? Territory {
            if let renderer = self.mapOfTerritory2Renderer[ter] {
                return renderer
            }
        }
        
        return MKOverlayRenderer()
    }
    
    // MARK: - Methods for TerritoryAnnotation
    func removeTerritoryAnnotationFromMap(_ ter:Territory) {
        if let theAnnotation = self.mapOfTerritory2Annotation[ter] {
            self.map.removeAnnotation(theAnnotation)
            self.mapOfTerritory2Annotation.removeValue(forKey: ter)
        }
    }
    
    func addTerritoryAnnotation2Map(_ ter:Territory) {
        let anno = TerritoryAnnotation(territory: ter)
        self.map.addAnnotation(anno)
        self.mapOfTerritory2Annotation[ter] = anno
    }
    
    fileprivate func refreshTerritoryDetailInfo(_ territory:Territory, callback:@escaping (_ detail:TerritoryInfo) -> Void) {
        RLClientActions.lookupTerritory(territory, callback: { (info) -> Void in
            self.mapOfTerritory2Detail[territory] = info
            
            DispatchQueue.main.async(execute: {
                self.removeTerritoryAnnotationFromMap(territory)
                self.addTerritoryAnnotation2Map(territory)
            })
            
            callback(info)
        })
    }
    
    fileprivate func refreshNamesOfAllMyTerritories() {
        guard let theUser = RLUser.getCurrentUser() else {return}
        
        for ter in theUser.readOnlyMyTerritories {
            self.mapOfTerritory2Detail[ter]?.ownerName = theUser.name
            
            self.removeTerritoryAnnotationFromMap(ter)
            self.addTerritoryAnnotation2Map(ter)
        }
    }
    
    fileprivate func cleanupMap() {
        for (ter, _) in self.mapOfTerritory2Renderer {
            self.map.removeOverlay(ter)
        }
        
        self.mapOfTerritory2Renderer.removeAll()
        
        for (_, anno) in self.mapOfTerritory2Annotation {
            self.map.removeAnnotation(anno)
        }
        self.mapOfTerritory2Detail.removeAll()
    }
    
    // MARK: - UIGestureRecognizerDelegate
    func gestureRecognizer(_ gestureRecognizer: UIGestureRecognizer, shouldRecognizeSimultaneouslyWith otherGestureRecognizer: UIGestureRecognizer) -> Bool {
        return true
    }
    
    // MARK: - Keyboard
    @objc func keyboardWillShow(_ notification: Notification) {
        if self.goverTerritoryView.isHidden {
            return
        }
        
        let dict = NSDictionary(dictionary: notification.userInfo!)
        let keyboardFrame = dict[UIResponder.keyboardFrameEndUserInfoKey] as! CGRect
        
        self.goverTerritoryView.onKeyboardWillShow(heightOfKeyobard: keyboardFrame.height)
    }
    
    @objc func keyboardWillHide(_ notification: Notification) {
        if self.goverTerritoryView.isHidden {
            return
        }
        
        self.goverTerritoryView.onKeyboardWillHide()
    }
    
    // MARK: - UIGestureRecognizer
    @objc func handlePanGesture(_ sender:UIPanGestureRecognizer) {
        self.driveModel = false
    }
    
    @objc func handleTapGesture(_ sender:UITapGestureRecognizer) {
        if self.map.region.span.longitudeDelta >= 0.1 {
            return
        }
        
        let locationInMapView = sender.location(in: self.map)
        let coordinate = self.map.convert(locationInMapView, toCoordinateFrom: self.map)
        
        self.initialVariablesOfTerritoryTapped()
        
        animationOfTerritoryTapped(coordinate) { () -> Void in
            self.animationFinishedOfTerritoryTapped = true
            self.triggerPopupInformationOfTerritoryTapped()
        }
        
        guard let theUser = RLUser.getCurrentUser() else {return}
        
        let ter = calculateTerritoryByLocation(coordinate)
        
        if !theUser.visitedTerritory(ter) {
            return
        }
        
        self.refreshTerritoryDetailInfo(ter) { (detail) -> Void in
            self.informationOfTerritoryTapped = detail
            self.triggerPopupInformationOfTerritoryTapped()
        }
    }
    
    // MARK: - PopupInformationOfTerritoryTapped
    fileprivate var animationFinishedOfTerritoryTapped = false
    fileprivate var informationOfTerritoryTapped:TerritoryInfo?
    fileprivate func initialVariablesOfTerritoryTapped() {
        self.animationFinishedOfTerritoryTapped = false
        self.informationOfTerritoryTapped = nil
    }
    
    // 在animationOfTerritoryTapped结束时和lookupTerritory结束时都调用一次,两个时间分别把animationFinishedOfTerritoryTapped设置为true以及把self.informationOfTerritoryTapped设置为非空
    fileprivate func triggerPopupInformationOfTerritoryTapped() {
        if !self.animationFinishedOfTerritoryTapped {
            return
        }
        
        if let theInfor = self.informationOfTerritoryTapped {
            DispatchQueue.main.async(execute: {
                self.territoryInforView.infor = theInfor

                self.showSubview(self.territoryInforView)
            })
        }
    }
    
    // MARK: - GADBannerViewDelegate
    func adViewWillLeaveApplication(_ bannerView: GADBannerView) {
        // do nothing
    }
    
    // MARK: - RLMyInformationViewControllerDelegate
    func myInformationViewControllerWillDismiss() {
        self.refreshMyResourceInfo()
    }
    
    // MARK: - RLTerritoryInforViewDelegate
    func backOnTerritoryInforView() {
        self.hideSubview(self.territoryInforView)
    }
    
    func attackOnTerritoryInforView(_ infor:TerritoryInfo) {
        self.hideSubview(self.territoryInforView)
        
        if let theUser = RLUser.getCurrentUser() {
            self.campaignView.setMaxCountOfSoldier2Campaign(min(theUser.countOfSoldier, theUser.countOfGold / PRICE_OF_EACH_SOLDIER_2_CAMPAIGN))
            self.campaignView.targetInfor = infor
            self.showSubview(self.campaignView)
        }
    }
    
    func configureOnTerritoryInforView(_ target: TerritoryInfo) {
        self.hideSubview(self.territoryInforView)
        
        if let theUser = RLUser.getCurrentUser() {
            self.goverTerritoryView.maxCountOfSoldier = theUser.countOfSoldier + target.armyQuantity
            self.goverTerritoryView.originalInfor = target
            self.showSubview(self.goverTerritoryView)
        }
    }
    
    // MARK: - RLAddSoldierViewDelegate
    func recruitOnAddSoldierView(_ countOfSoldier2Recruit:Int) {
        RLClientActions.recruitSoldier(countOfSoldier2Recruit) { () -> Void in
            DispatchQueue.main.async(execute: {
                self.refreshMyResourceInfo()
            })
        }
        
        self.hideSubview(self.addSoldierView)
    }
    
    func backOnAddSoldierView() {
        self.hideSubview(self.addSoldierView)
    }
    
    // MARK: - RLAddDiamondViewDelegate
    func buyOnAddDiamond() {
        self.hideSubview(self.addDiamondView)
        
        self.purchase()
    }
    
    func cancelOnAddDiamond() {
        self.hideSubview(self.addDiamondView)
    }
    
    // MARK: - RLCampaignViewDelegate
    func campaignOnCampaignView(_ countOfSoldier2Campaign:Int, targetInfor: TerritoryInfo) {
        
        RLClientActions.attack(countOfSoldier2Campaign, latitude100: targetInfor.latitude100, longitude100: targetInfor.longitude100) { (fightResult) -> Void in
            DispatchQueue.main.async(execute: {
                self.hideSubview(self.campaignView)
                
                if let theUser = RLUser.getCurrentUser() {
                    theUser.updateMyTerritoriesOnFightResult(fightResult, target: targetInfor)
                    theUser.countOfGold = theUser.countOfGold - fightResult.goldCost
                    theUser.countOfSoldier = theUser.countOfSoldier - countOfSoldier2Campaign
                    self.mapOfTerritory2Renderer[Territory(latitude100: targetInfor.latitude100, longitude100: targetInfor.longitude100)]?.setNeedsDisplay()
                }
                
                self.refreshMyResourceInfo()
                self.refreshTerritoryDetailInfo(Territory(latitude100: targetInfor.latitude100, longitude100: targetInfor.longitude100), callback: { (detail) -> Void in
                    // do nothing
                })
                self.fightResultView.fightResult = fightResult
                self.showSubview(self.fightResultView)
            })
        }
    }
    
    func cancelOnCampaignView() {
        self.hideSubview(self.campaignView)
    }
    
    // MARK: - RLFightResultViewDelegate
    func okOnFightResultView() {
        self.hideSubview(self.fightResultView)
        
        self.refreshCountOfMyNewFights()
    }
    
    // MARK: - RLGoverTerritoryViewDelegate
    func okOnGoverTerritoryView(_ oldInfor:TerritoryInfo, newName: String, newCountOfSoldier: Int) {
        RLClientActions.gover(newName, newCountOfSoldier: newCountOfSoldier, latitude100: oldInfor.latitude100, longitude100: oldInfor.longitude100) { (countOfSoliderLeft) -> Void in
            if let theUser = RLUser.getCurrentUser() {
                theUser.countOfSoldier = countOfSoliderLeft
                
                self.refreshTerritoryDetailInfo(Territory(latitude100: oldInfor.latitude100, longitude100: oldInfor.longitude100), callback: { (detail) -> Void in
                    // do nothing
                    })
                
                DispatchQueue.main.async(execute: {
                    self.refreshMyResourceInfo()
                    self.hideSubview(self.goverTerritoryView)
                })
            }
        }
    }
    
    func cancelOnGoverTerritoryView() {
        self.hideSubview(self.goverTerritoryView)
    }
    
    // MARK: - RLUpdateVersionViewDelegate
    func onUpdateVersion() {
        UIApplication.shared.open(URL(string: CURRENT_APP_DOWNLOAD_URL)!, options: [UIApplication.OpenExternalURLOptionsKey : Any](), completionHandler: nil)
    }
    
    // MARK: - RLTrainingProgressViewDelegate
    func quickFinishOnTrainingProgressView() {
        RLClientActions.quickFinishTraining { (errorCode) -> Void in
            if errorCode != ERROR_NONE {
                return
            }
            
            DispatchQueue.main.async(execute: {
                self.refreshMyResourceInfo()
            })
            
        }
        self.hideSubview(self.trainingProgressView)
    }
    
    func iknowOnTrainingProgressView() {
        self.hideSubview(self.trainingProgressView)
    }
    
    // MARK: - RLMyFightsViewDelegate
    func iKnowOnMyFightsView() {
        self.hideSubview(self.myFightsView)
        RLUser.saveNowAsLastTimeOfCheckMyFights()
        self.refreshCountOfMyNewFights()
    }
    
    func gotoLocationOnMyFightsView(_ latitude100: Int, longitude100: Int) {        
        self.driveModel = false
        
        let lat = latitude100 >= 0 ? (CLLocationDegrees(latitude100) + 0.5)/100 : (CLLocationDegrees(latitude100) - 0.5)/100
        let lon = longitude100 >= 0 ? (CLLocationDegrees(longitude100) + 0.5)/100 : (CLLocationDegrees(longitude100) - 0.5)/100
        self.moveRegionOfMapTo(CLLocationCoordinate2D(latitude: lat, longitude: lon))
    }
    
    // MARK: - RLRequestHealthViewDelegate
    func activateOnRequestHealthView() {
        if let theHealthKitStore = self.healthKitStore {
            let stepCountType = HKQuantityType.quantityType(forIdentifier: HKQuantityTypeIdentifier.stepCount)!
            
            let healthKitTypesToRead:Set<HKObjectType> = [stepCountType]
            theHealthKitStore.requestAuthorization(toShare: nil, read: healthKitTypesToRead) { (success, error) -> Void in
                printLog(success)
            }
        }
        
        self.hideSubview(self.requestHealthView)
    }
    
    // MARK: - GKGameCenterControllerDelegate
    func gameCenterViewControllerDidFinish(_ gameCenterViewController: GKGameCenterViewController) {
        self.dismiss(animated: true, completion: nil)
    }
    
    // MARK: - SKProductsRequestDelegate
    func productsRequest(_ request: SKProductsRequest, didReceive response: SKProductsResponse) {
        let productsPurchased = response.products
        if productsPurchased.count == 0 {
            return
        }
        
        productsPurchased.forEach { (product) -> () in
            switch product.productIdentifier {
            case INAPP_PURCHASE_DIAMOND_50:
                let payment = SKPayment(product: product)
                SKPaymentQueue.default().add(payment)
            default: break
            }
        }
    }
    
    func request(_ request: SKRequest, didFailWithError error: Error) {
        printLog("request failed:\(error)")
    }
    
    func requestDidFinish(_ request: SKRequest) {
        printLog("request finished")
    }
    
    // MARK: - SKPaymentTransactionObserver
    func paymentQueue(_ queue: SKPaymentQueue, updatedTransactions transactions: [SKPaymentTransaction]) {
        transactions.forEach { (tran) -> () in
            switch tran.transactionState {
            case .purchased:
                printLog("交易完成")
                RLClientActions.purchase(tran.payment.productIdentifier, callback: { (countOfDiamond) -> Void in
                    guard let theUser = RLUser.getCurrentUser() else {return}
                    theUser.countOfDiamond = theUser.countOfDiamond + countOfDiamond
                    
                    DispatchQueue.main.async(execute: {
                        self.refreshMyResourceInfo()
                    })
                })
                
                SKPaymentQueue.default().finishTransaction(tran)
            case .purchasing:
                printLog("商品添加进列表")
            case .restored:
                printLog("已经购买过商品")
            case .failed:
                printLog("交易失败")
                SKPaymentQueue.default().finishTransaction(tran)
            case .deferred:
                printLog("等待其它活动中...")
            }
        }
    }
        
    // MARK: - IBActions
    @IBAction func myNameButtonPressed() {
        if let vc = self.storyboard?.instantiateViewController(withIdentifier: "myinformation") as? RLMyInformationViewController {
            vc.delegate = self
            self.present(vc, animated: true) {
                // do nothing
            }
        }
    }
    
    @IBAction func ask2SwitchAccountOrNot() {
        let alertController = UIAlertController(title: "游戏帐户与GameCenter不一致", message: "是否要以GameCenter帐户重新登录游戏", preferredStyle: UIAlertController.Style.alert)
        
        alertController.addAction(UIAlertAction(title: "确定", style: UIAlertAction.Style.default) { (action) -> Void in
            self.cleanupMap()
            RLUser.cleanupSavedFootprints()
            self.showSubview(self.loadingView)
            self.handleGameCenterLoginSuccess(GKLocalPlayer.local)
        })
        alertController.addAction(UIAlertAction(title:"取消", style:UIAlertAction.Style.cancel, handler: nil))
        self.present(alertController, animated: true) { () -> Void in
            self.animateHideTipOfUnmatchedGameCenterID()
        }
    }
    @IBAction func showRank() {
        let leaderboard = GKGameCenterViewController()
        leaderboard.gameCenterDelegate = self
        self.present(leaderboard, animated: true, completion: nil)
    }
    
    @IBAction func zan() {
        let alertController = UIAlertController(title: "喜欢这个应用", message: nil, preferredStyle: UIAlertController.Style.actionSheet)
        alertController.addAction(UIAlertAction(title:"推荐给微信好友", style:UIAlertAction.Style.default, handler:{(action) -> Void in
            self.recommend2WeixinFriend()
        }))
        /*
        Tencent
        alertController.addAction(UIAlertAction(title:"推荐给QQ好友", style:UIAlertActionStyle.Default, handler:{(action) -> Void in
        self.recommend2QQFriend()
        }))
        */
        alertController.addAction(UIAlertAction(title:"给个好评", style:UIAlertAction.Style.default, handler:{(action) -> Void in
            self.reviewThisApp()
        }))
        alertController.addAction(UIAlertAction(title:"取消", style:UIAlertAction.Style.cancel, handler:nil))
        
        self.present(alertController, animated: true, completion: nil)
    }
    
    fileprivate func reviewThisApp() {
        UIApplication.shared.open(URL(string:REVIEW_APP_URL)!, options: [UIApplication.OpenExternalURLOptionsKey : Any](), completionHandler: nil)
    }
    
    fileprivate func recommend2WeixinFriend() {
        let req = SendMessageToWXReq()
        req.scene = Int32(WXSceneSession.rawValue) // WXSceneTimeline.value表示发到朋友圈
        
        req.bText = false
        req.message = WXMediaMessage()
        req.message.title = "世界是我们的"
        req.message.description = "一起来享受攻城略地的快感吧！下载地址:\(CURRENT_APP_DOWNLOAD_URL)"
        req.message.setThumbImage(UIImage(named:"logo.png")!)
        
        let ext = WXWebpageObject()
        ext.webpageUrl = CURRENT_APP_DOWNLOAD_URL
        req.message.mediaObject = ext;
        
        WXApi.send(req)
    }
    
    @IBAction func viewMessages() {
        RLClientActions.viewBriefFights { (fightsAsAttacker, fightsAsDefender) -> Void in
            // do nothing
            DispatchQueue.main.async(execute: {
                self.myFightsView.allMyFights = (fightsAsAttacker, fightsAsDefender)
                self.showSubview(self.myFightsView)
            })
        }
    }
    
    @IBAction func readStepAsCoin() {
        self.checkAuthStatusOfHealthKitStore()

        self.readStepsOfToday { (stepCountOfToday, error) -> Void in
            if error != nil {
                return
            }
            
            RLClientActions.updateStep(stepCountOfToday, callback: { (goldPlus:Int) -> Void in
                if let theUser = RLUser.getCurrentUser() {
                    theUser.countOfGold = goldPlus + theUser.countOfGold
                    DispatchQueue.main.async(execute: {
                        let sizeOfButton = self.readStepButton.bounds.size
                        let point = self.readStepButton.convert(CGPoint(x: sizeOfButton.width/2, y: sizeOfButton.height/2), to: self.view)
                        self.animateGoldEarned(goldPlus, fromPoint: point)
                        self.refreshMyResourceInfo()
                    })
                }
            })
        }
    }
    
    @IBAction func gotoMyLocation() {        
        let userCoordinate = self.map.userLocation.coordinate
        if !validateCoordinate(userCoordinate) {
            return
        }
        
        self.driveModel = false
        self.moveRegionOfMapTo(userCoordinate)
        self.driveModel = true
    }
    
    @IBAction func addDiamond() {
        self.showSubview(self.addDiamondView)
    }
    @IBAction func addSoldier() {
        if let theUser = RLUser.getCurrentUser() {
            self.addSoldierView.setMaxCountOfRecruit(theUser.countOfGold / PRICE_OF_EACH_SOLDIOR_2_RECRUIT)
            self.showSubview(self.addSoldierView)
        }
    }
    @IBAction func checkTrainingProgress() {
        guard let theUser = RLUser.getCurrentUser() else {return}
        guard let theTraining = theUser.training else {return}
        self.trainingProgressView.setTraining(theTraining)
        
        self.showSubview(self.trainingProgressView)
    }
    
    // MARK: - Instance Method
    private func ad() {
        // Always Show View
        let adSize = GADAdSizeFullWidthPortraitWithHeight(50) // 当View Did Appear之后,GADAdSizeFullWidthPortraitWithHeight才能拿到屏幕宽度
        let admobBannerView = GADBannerView(adSize: adSize, origin: CGPoint(x: 0, y: self.view.safeAreaInsets.top))
        self.view.addSubview(admobBannerView)
        admobBannerView.rootViewController = self
        let req = GADRequest()
        /*
         * 这是正式的UnitID
         */
        admobBannerView.adUnitID = "ca-app-pub-9409825561491259/5230527690"
        req.testDevices = [kGADSimulatorID, "958fb333948ef8d09afed7c9eafea6e9", "ea4270fcbcf9c9a7750676e84945faf6"]
        admobBannerView.delegate = self
        /*
         6p (414.0, 736.0)
         6  (375.0, 667.0)
         5  (320.0, 568.0)
         4  (320.0, 480.0)
         */
        admobBannerView.load(req)
    }
    
    private func purchase() {
        if SKPaymentQueue.canMakePayments() {
            let productSet : Set<String> = [INAPP_PURCHASE_DIAMOND_50]
            let request = SKProductsRequest(productIdentifiers: productSet)
            request.delegate = self
            request.start()
        } else {
            let alert = WLUI.alert(title: "未开启应用内购买", message: nil)
            self.present(alert, animated: true, completion: nil)
        }
    }
    
    fileprivate func loadCustomViews() {
        self.updateVersionView = UIView.fromNib("RLUpdateVersionView")
        self.view.addSubview(self.updateVersionView)
        self.updateVersionView.delegate = self
        self.updateVersionView.frame = self.view.bounds
        self.hideSubview(self.updateVersionView)
        
        self.requestHealthView = UIView.fromNib("RLRequestHealthView")
        self.view.addSubview(self.requestHealthView)
        self.requestHealthView.delegate = self
        self.requestHealthView.frame = self.view.bounds
        self.hideSubview(self.requestHealthView)
        
        self.territoryInforView = UIView.fromNib("RLTerritoryInforView")
        self.view.addSubview(self.territoryInforView)
        self.territoryInforView.delegate = self
        self.territoryInforView.frame = self.view.bounds
        self.hideSubview(self.territoryInforView)
        
        self.addSoldierView = UIView.fromNib("RLAddSoldierView")
        self.view.addSubview(self.addSoldierView)
        self.addSoldierView.delegate = self
        self.addSoldierView.frame = self.view.bounds
        self.hideSubview(self.addSoldierView)
        
        self.addDiamondView = UIView.fromNib("RLAddDiamondView")
        self.view.addSubview(self.addDiamondView)
        self.addDiamondView.delegate = self
        self.addDiamondView.frame = self.view.bounds
        self.hideSubview(self.addDiamondView)
        
        self.campaignView = UIView.fromNib("RLCampaignView")
        self.view.addSubview(self.campaignView)
        self.campaignView.delegate = self
        self.campaignView.frame = self.view.bounds
        self.hideSubview(self.campaignView)
        
        self.fightResultView = UIView.fromNib("RLFightResultView")
        self.view.addSubview(self.fightResultView)
        self.fightResultView.delegate = self
        self.fightResultView.frame = self.view.bounds
        self.hideSubview(self.fightResultView)
        
        self.goverTerritoryView = UIView.fromNib("RLGoverTerritoryView")
        self.view.addSubview(self.goverTerritoryView)
        self.goverTerritoryView.delegate = self
        self.goverTerritoryView.frame = self.view.bounds
        self.hideSubview(self.goverTerritoryView)
        
        self.trainingProgressView = UIView.fromNib("RLTrainingProgressView")
        self.view.addSubview(self.trainingProgressView)
        self.trainingProgressView.delegate = self
        self.trainingProgressView.frame = self.view.bounds
        self.hideSubview(self.trainingProgressView)
        
        self.myFightsView = UIView.fromNib("RLMyFightsView")
        self.myFightsView.prepareFightsInfoTableView()
        self.view.addSubview(self.myFightsView)
        self.myFightsView.delegate = self
        self.myFightsView.frame = self.view.bounds
        self.hideSubview(self.myFightsView)
    }
    
    fileprivate func showSubview(_ view:UIView) {
        view.isHidden = false
        self.view.bringSubviewToFront(view)
    }
    
    fileprivate func hideSubview(_ view:UIView) {
        view.isHidden = true
        self.view.sendSubviewToBack(view)
    }
    
    fileprivate func moveRegionOfMapTo(_ targetCoordinate:CLLocationCoordinate2D) {
        let currentRegion = self.map.region
        let currentCenter = currentRegion.center
        let currentSpan = currentRegion.span
        
        let latitudeDelta = abs(currentCenter.latitude-targetCoordinate.latitude)
        let longitudeDelta = abs(currentCenter.longitude-targetCoordinate.longitude)
        if latitudeDelta < currentSpan.latitudeDelta/2 && longitudeDelta < currentSpan.longitudeDelta/2 {
            // 经度和纬度都在视图范围内
            self.map.setRegion(MKCoordinateRegion.init(center: targetCoordinate, span: MKCoordinateSpan(latitudeDelta: 0.02, longitudeDelta: 0.02)), animated: true)
        }
        else {
            // 经度或纬度在视图范围外
            let globalRegion = MKCoordinateRegion.init(center: targetCoordinate, span: MKCoordinateSpan(latitudeDelta: min(max(latitudeDelta, longitudeDelta)*2.2, 160), longitudeDelta: min(max(latitudeDelta, longitudeDelta)*2.2, 360)))
            
            self.map.setRegion(globalRegion, animated: true)
            // 如果setRegion:animated还能加一个complete参数就好了
            DispatchQueue.main.asyncAfter(deadline: DispatchTime.now() + Double(Int64(1 * NSEC_PER_SEC)) / Double(NSEC_PER_SEC)) { () -> Void in
                self.moveRegionOfMapTo(targetCoordinate)
            }
        }
    }
    
    fileprivate func checkAuthStatusOfHealthKitStore() {
        if HKHealthStore.isHealthDataAvailable() {
            self.healthKitStore = HKHealthStore()
            let stepCountType = HKQuantityType.quantityType(forIdentifier: HKQuantityTypeIdentifier.stepCount)!
            
            if self.healthKitStore.authorizationStatus(for: stepCountType) == .notDetermined {
                self.showSubview(self.requestHealthView)
            }
        }
    }
    
    fileprivate func registerGestureRecognizer() {
        let pan = UIPanGestureRecognizer(target: self, action: #selector(ViewController.handlePanGesture(_:)))
        self.map.addGestureRecognizer(pan)
        /*
         * MKMapView内部实现时，已添加了1个UIPanGestureRecognizer，而这里我们又添加了另外1个UIPanGestureRecognizer，也就是说同1个MKMapView有两个相同类型的手势辨认，但是运行时内部默许相同类型的手势辨认只有1个会得到处理，所以第1段代码始终没有输出handlePan。幸亏UIPanGestureRecognizerDelegate提供了gestureRecognizer:shouldRecognizeSimultaneouslyWithGestureRecognizer方法，该方法返回YES时，意味着所有相同类型的手势辨认都会得到处理。
         */
        pan.delegate = self
        
        let tap = UITapGestureRecognizer(target: self, action: #selector(ViewController.handleTapGesture(_:)))
        self.map.addGestureRecognizer(tap)
    }
    
    fileprivate func setProgress(_ progress:RLProgress) {
        self.loadingProgressView.setProgress(progress.getProgress(), animated: true)
        self.loadingMessageLabel.text = progress.getProgressMessage()
        
        if progress == .done {
            DispatchQueue.main.asyncAfter(deadline: DispatchTime.now() + Double(Int64(2 * NSEC_PER_SEC)) / Double(NSEC_PER_SEC)) { () -> Void in
                self.hideSubview(self.loadingView)
                
                self.ad()
            }
        }
    }
    
    fileprivate func animationOfTerritoryTapped(_ coordinate:CLLocationCoordinate2D, callbackAfterAnimation:@escaping () -> Void) {
        let latitudeOfCenter:CLLocationDegrees
        let longitudeOfCenter:CLLocationDegrees
        
        let latitude100 = Int(coordinate.latitude * 100)
        let longitude100 = Int(coordinate.longitude * 100)
        
        if coordinate.latitude >= 0 {
            latitudeOfCenter = Double(latitude100)/Double(100) + 0.005
        } else {
            latitudeOfCenter = Double(latitude100)/Double(100) - 0.005
        }
        
        if coordinate.longitude >= 0 {
            longitudeOfCenter = Double(longitude100)/Double(100) + 0.005
        } else {
            longitudeOfCenter = Double(longitude100)/Double(100) - 0.005
        }
        
        let territoryBounds = self.map.convert(MKCoordinateRegion(
            center: CLLocationCoordinate2D(latitude: latitudeOfCenter, longitude: longitudeOfCenter),
            span: MKCoordinateSpan(latitudeDelta: 0.01, longitudeDelta: 0.01)), toRectTo: self.view)
        let blackTerritory = UIView(frame: territoryBounds)
        blackTerritory.backgroundColor = UIColor.black
        blackTerritory.alpha = 0
        self.animationViewOnMapTapped.addSubview(blackTerritory)
        
        self.showSubview(self.animationViewOnMapTapped)
        UIView.animate(withDuration: 0.4, animations: { () -> Void in
            blackTerritory.alpha = 0.5
        }, completion: { (finished) -> Void in
            UIView.animate(withDuration: 0.4, animations: { () -> Void in
                blackTerritory.alpha = 0
            }, completion: { (finished) -> Void in
                        
                blackTerritory.removeFromSuperview()
                self.hideSubview(self.animationViewOnMapTapped)
                
                callbackAfterAnimation()
            })
        }) 
    }
    
    fileprivate func refreshCountOfMyNewFights() {
        RLClientActions.fetchCountOfNewFights { (count) -> Void in
            DispatchQueue.main.async(execute: {
                if count == 0 {
                    self.imageOfCountOfNewFights.isHidden = true
                } else {
                    self.imageOfCountOfNewFights.isHidden = false
                    self.imageOfCountOfNewFights.image = drawMark(count, sizeOfFont: 10, sizeOfImage: self.imageOfCountOfNewFights.bounds.size)
                    self.imageOfCountOfNewFights.layer.cornerRadius = self.imageOfCountOfNewFights.bounds.width/2
                    self.imageOfCountOfNewFights.clipsToBounds = true
                }
            })
        }
    }
    
    fileprivate func refreshMyResourceInfo() {
        guard let theUser = RLUser.getCurrentUser() else {return}
        
        self.myNameButton.setTitle(theUser.name, for: .normal)
        
        let isTrainingSoldier = theUser.isTrainingSoldier
        self.checkTrainingProgressButton.isHidden = !isTrainingSoldier
        self.recruitSoldierButton.isHidden = isTrainingSoldier

        let numberFormatter = NumberFormatter()
        numberFormatter.numberStyle = NumberFormatter.Style.decimal
        
        self.countOfGoldLabel.text = numberFormatter.string(from: NSNumber.init(value: theUser.countOfGold))
        self.countOfSoldierLabel.text = numberFormatter.string(from: NSNumber.init(value:theUser.countOfSoldier))
        self.countOfDiamondLabel.text = numberFormatter.string(from: NSNumber.init(value:theUser.readOnlyCountOfDiamond))
    }
    
    fileprivate func animateGoldEarned(_ countOfGold:Int, fromPoint:CGPoint) {
        let sizeOfImage:CGFloat = 15
        let widthOfScoreLabel:CGFloat = 45
        let heightOfScoreLabel:CGFloat = 15
        
        var goldImages = [UIImageView]()
        if countOfGold > 0 {
            for _ in 0 ..< countOfGold/100 + 1 {
                let goldImage = UIImageView(image: UIImage(named: "gold.png"))
                goldImage.frame = CGRect(x: fromPoint.x-sizeOfImage/2, y: fromPoint.y-sizeOfImage/2, width: sizeOfImage, height: sizeOfImage)
                self.view.addSubview(goldImage)
                
                goldImages.append(goldImage)
            }
        }
        
        let scoreLabel = UILabel(frame:CGRect(x: fromPoint.x-widthOfScoreLabel/2,y: fromPoint.y-heightOfScoreLabel/2,width: widthOfScoreLabel,height: heightOfScoreLabel))
        self.view.addSubview(scoreLabel)
        scoreLabel.text = "\(countOfGold)"
        if countOfGold >= 0 {
            scoreLabel.textColor = UIColor.red
        } else {
            scoreLabel.textColor = UIColor.black
        }
        scoreLabel.textAlignment = NSTextAlignment.center
        scoreLabel.font = UIFont.boldSystemFont(ofSize: 9)
        scoreLabel.adjustsFontSizeToFitWidth = true
        
        goldImages.forEach({ (view) -> () in
            view.alpha = 0.5
        })
        UIView.animate(withDuration: 2, animations: { () -> Void in
            scoreLabel.center = CGPoint(x: fromPoint.x, y: fromPoint.y-40)
            
            goldImages.forEach({ (view) -> () in
                view.alpha = 1
                
                view.center = CGPoint(x: fromPoint.x + CGFloat(arc4random().hashValue % 20), y: fromPoint.y + CGFloat(arc4random().hashValue % 20))
            })
            }, completion: { (finished) -> Void in
                if finished {
                    UIView.animate(withDuration: 1, animations: { () -> Void in
                        scoreLabel.alpha = 0
                        }, completion: { (finished) -> Void in
                            scoreLabel.removeFromSuperview()
                    })
                    
                    let sizeOfImageOfMyGoldResource = self.imageOfMyGoldResource.bounds.size
                    let destinationOfGoldImage = self.imageOfMyGoldResource.convert(CGPoint(x: sizeOfImageOfMyGoldResource.width/2, y: sizeOfImageOfMyGoldResource.height/2), to: self.view)
                    
                    goldImages.forEach({ (view) -> () in
                        UIView.animate(withDuration: Double(150 + arc4random().hashValue % 20) / 100, animations: { () -> Void in
                            view.center = destinationOfGoldImage
                            }, completion: { (finished) -> Void in
                                view.removeFromSuperview()
                        })
                    })
                }
        }) 
    }
    
    fileprivate func try2AddNewFootprint(_ fp : Territory) {
        guard let theUser = RLUser.getCurrentUser() else {
            printLog("用户尚未登录:延迟2秒添加Footprint")
            DispatchQueue.main.asyncAfter(deadline: DispatchTime.now() + Double(Int64(2 * NSEC_PER_SEC)) / Double(NSEC_PER_SEC)) { () -> Void in
                self.try2AddNewFootprint(fp)
            }
            
            return
        }
        
        if !fp.isEqual(self.lastTerritoryIAmIn) {
            RLClientActions.searchTreasure(fp, callback: { (goldFound:Int) -> Void in
                theUser.countOfGold = theUser.countOfGold + goldFound
                
                DispatchQueue.main.async(execute: {
                    
                    if !self.map.isUserLocationVisible {
                        return
                    }
                    
                    if let theLocation = self.map.userLocation.location {
                        let coordinate = theLocation.coordinate
                        
                        let point = self.map.convert(coordinate, toPointTo: self.view)
                        
                        self.animateGoldEarned(goldFound, fromPoint: point)
                    }
                    
                    self.refreshMyResourceInfo()
                })
            })
        }
        
        if !theUser.readOnlyFootprints.contains(fp) {
            theUser.insertFootprint(fp)
            self.ensuerTerritoryInMap(fp)
            
            RLClientActions.addFootprint(fp)
        }
        
        self.lastTerritoryIAmIn = fp
    }
    
    fileprivate func ensuerTerritoryInMap(_ territory:Territory) {
        if self.mapOfTerritory2Renderer[territory] == nil {
            let render = TerritoryRenderer(territory: territory)
            self.mapOfTerritory2Renderer[territory] = render
            
            self.map.addOverlay(territory)
        }
    }
    
    // MARK: - HealthKit
    fileprivate func readStepsOfToday(_ callback:@escaping (_ stepCountOfToday:Int, _ error:Error?) -> Void) {
        if !HKHealthStore.isHealthDataAvailable() {
            return
        }
        guard let theHealthKitStore = self.healthKitStore else {return}
        
        let calendar = Calendar.current
        let now = Date()
        
        let components = (calendar as NSCalendar).components(NSCalendar.Unit.year.union(.month).union(.day), from: now)
        
        let startDate = calendar.date(from: components)
        let endDate = (calendar as NSCalendar).date(byAdding: NSCalendar.Unit.day, value: 1, to: startDate!, options: NSCalendar.Options(rawValue: 0))
        
        let sampleType = HKSampleType.quantityType(forIdentifier: HKQuantityTypeIdentifier.stepCount)
        let predicate = HKQuery.predicateForSamples(withStart: startDate, end: endDate, options: HKQueryOptions())
        
        let query = HKSampleQuery(sampleType: sampleType!, predicate: predicate, limit: 0, sortDescriptors: nil) {
            query, results, error in
            /*
             * 统计不同的device记录的步数
             * 比如Apple Watch记录步数为5600, iPhone记录步数为6300
             * 最后调用callback时把步数大的那一个传进去
             */
            var datas = [HKSource : Int]()

            if error == nil {
                for sample in results! {
                    if let quantity = sample as? HKQuantitySample {
                        let steps = Int(quantity.quantity.doubleValue(for: HKUnit.count()))
                        if let stepOfSource = datas[quantity.sourceRevision.source] {
                            datas[quantity.sourceRevision.source] = stepOfSource + steps
                        } else {
                            datas[quantity.sourceRevision.source] = steps
                        }
                    }
                }
            }
            
            var maxStep = 0
            for (_, step) in datas {
                maxStep = max(maxStep, step)
            }
            
            callback(maxStep, error)
        }
        
        theHealthKitStore.execute(query)
    }
    
    // MARK: - Login Methods
    fileprivate func login() {
        if let _ = RLUser.getUUIDLastSuccessLogin() {
            self.loginIgnoreGameCenter({ () -> Void in
                self.authenticateLocalUser()
            })
        } else {
            self.setProgress(.gameCenterLogining)
            
            self.authenticateLocalUser()
        }
    }
    
    fileprivate func authenticateLocalUser() {
        let localPlayer = GKLocalPlayer.local
        localPlayer.authenticateHandler = {(loginViewController, error) -> Void in
            var doLoginIgnoreGameCenter = false
            
            if error != nil {
                // 如果登录GameCenter有error,在当前系统没有User时,标记在最后以忽略GameCenter的方式登录
                printLog("\(String(describing: error))")
                
                if let _ = RLUser.getCurrentUser() {
                    // do nothing
                } else {
                    doLoginIgnoreGameCenter = true
                }
            } else if localPlayer.isAuthenticated {
                /*
                * 如果GameCenter帐户登录成功
                * ------当前系统有User时,并且User的uuid与GameCenter的帐号不匹配时,提示要不要以当前GameCenter帐号重新登录游戏
                * ------当前系统没有User时,就以localPlayer登录之
                */
                if let theUser = RLUser.getCurrentUser() {
                    if !theUser.matchCurrentGameCenterID() {
                        // 界面上提示,你的GameCenter帐户不一致了,点击之后,直接调用self.handleGameCenterLoginSuccess(localPlayer)
                        self.animateShowTipOfUnmatchedGameCenterID()
                    }
                } else {
                    self.handleGameCenterLoginSuccess(localPlayer)
                }
            } else if loginViewController != nil {
                /*
                * GameCenter登录ViewController可用时,就弹出来让登录吧,即使当前系统已经有的User也弹出来
                * 因为当前系统的User可能非GameCenter帐号,也可能是别的GameCenter帐号的,这两种情况都不大好
                */
                self.present(loginViewController!, animated: true, completion: { () -> Void in
                })
            } else {
                // 其他情况,同error时的处理方法一样
                if let _ = RLUser.getCurrentUser() {
                    // do nothing
                } else {
                    doLoginIgnoreGameCenter = true
                }
            }
            
            if doLoginIgnoreGameCenter {
                self.loginIgnoreGameCenter({ () -> Void in
                    // do nothing
                })
            }
        }
    }
    
    fileprivate func animateShowTipOfUnmatchedGameCenterID() {
        self.showSubview(self.unmatchedAccountTipButton)
        UIView.animate(withDuration: 2, animations: { () -> Void in
            self.unmatchedAccountTipButton.alpha = 1
        }) 
        
        DispatchQueue.main.asyncAfter(deadline: DispatchTime.now() + Double(Int64(15 * NSEC_PER_SEC)) / Double(NSEC_PER_SEC)) { () -> Void in
            self.animateHideTipOfUnmatchedGameCenterID()
        }
    }
    
    fileprivate func animateHideTipOfUnmatchedGameCenterID() {
        if self.unmatchedAccountTipButton.alpha == 1 {
            UIView.animate(withDuration: 2, animations: { () -> Void in
                self.unmatchedAccountTipButton.alpha = 0
                }, completion: { (finished) -> Void in
                    self.hideSubview(self.unmatchedAccountTipButton)
            })
        }
    }
    
    fileprivate func loginCallback(_ success:Bool) {
        if success {
            if let theUser = RLUser.getCurrentUser() {
                
                // self.map.addOverlay必须是在main_queue里面才行
                DispatchQueue.main.async(execute: {
                    self.refreshMyResourceInfo()
                    
                    for fp in theUser.readOnlyFootprints {
                        self.ensuerTerritoryInMap(fp)
                    }
                    
                    self.setProgress(.done)
                    self.refreshCountOfMyNewFights()
                })
            }
        } else {
            self.showSubview(self.updateVersionView)
        }
    }
    
    fileprivate func loginIgnoreGameCenter(_ afterLogin:@escaping () -> Void) {
        DispatchQueue.main.async(execute: {
            self.setProgress(.getFootprints)
        })
        
        if let savedAccount = RLUser.getUUIDLastSuccessLogin() {
            RLClientActions.login(savedAccount, nameOfPlayer: RLUser.getNameLastSuccesLogin(), callback: { (success:Bool) -> Void in
                self.loginCallback(success)
                
                afterLogin()
            })
        } else {
            RLClientActions.registerAndLogin({ (success:Bool) -> Void in
                self.loginCallback(success)
            })
        }
    }
    
    fileprivate func handleGameCenterLoginSuccess(_ localPlayer:GKLocalPlayer) {
        DispatchQueue.main.async(execute: {
            self.setProgress(.getFootprints)
        })
        
        RLClientActions.login(localPlayer) { (success:Bool) -> Void in
            self.loginCallback(success)
        }
    }
}

fileprivate func calculateTerritoryByLocation(_ coordinate: CLLocationCoordinate2D) -> Territory {
    return Territory(
        latitude100: Int(coordinate.latitude * 100),
        longitude100: Int(coordinate.longitude * 100))
}

fileprivate func calculateTerritoriesByRegion(_ region:MKCoordinateRegion) -> Set<Territory> {
    var territories = Set<Territory>()
    
    let centerOfRegion = region.center
    let spanOfRegion = region.span
    
    let left = centerOfRegion.longitude - spanOfRegion.longitudeDelta / 2
    let right = centerOfRegion.longitude + spanOfRegion.longitudeDelta / 2
    let top = centerOfRegion.latitude + spanOfRegion.latitudeDelta / 2
    let bottom = centerOfRegion.latitude - spanOfRegion.latitudeDelta / 2
    
    let left100 = left >= 0 ? Int(left * 100) : Int((left - 0.01) * 100)
    let right100 = left >= 0 ? Int(right * 100) : Int((right - 0.01) * 100)
    let top100 = left >= 0 ? Int(top * 100) : Int((top - 0.01) * 100)
    let bottom100 = left >= 0 ? Int(bottom * 100) : Int((bottom - 0.01) * 100)
    
    for lon100 in left100 ..< right100 + 1 {
        for lat100 in bottom100 ..< top100 + 1 {
            territories.insert(Territory(latitude100: lat100, longitude100: lon100))
        }
    }
    
    return territories
}

fileprivate func validateCoordinate(_ coordinate:CLLocationCoordinate2D) -> Bool {
    return coordinate.latitude >= -90 && coordinate.latitude <= 90 && coordinate.longitude >= -180 && coordinate.longitude <= 180 && !(coordinate.latitude == 0 && coordinate.longitude == 0)
}

enum RLProgress {
    case gameCenterLogining, getFootprints, done
    
    fileprivate func getProgress() -> Float {
        switch self {
        case .gameCenterLogining:
            return 0.1
        case .getFootprints:
            return 0.5
        case .done:
            return 1
        }
    }
    
    fileprivate func getProgressMessage() -> String {
        switch self {
        case .gameCenterLogining:
            return "登录GameCenter(请耐心等待)"
        case .getFootprints:
            return "获取足迹"
        case .done:
            return "完成"
        }
    }
}

class MyFootprint:NSObject {
    let when:Date
    let coordinate:CLLocationCoordinate2D
    let angle:Double
    
    init(currentCoordinate:CLLocationCoordinate2D, lastCoordinate:CLLocationCoordinate2D?) {
        self.when = Date()
        self.coordinate = currentCoordinate
        if let theLastCoordinate = lastCoordinate {
            let latitudeDelta = currentCoordinate.latitude - theLastCoordinate.latitude
            let longitudeDelta = currentCoordinate.longitude - theLastCoordinate.longitude
            
            if latitudeDelta == 0 {
                if longitudeDelta >= 0 {
                    self.angle = 0
                } else {
                    self.angle = -Double.pi
                }
            } else {
                let angleOfArctan = atan(longitudeDelta/latitudeDelta)
                if latitudeDelta < 0 {
                    self.angle = angleOfArctan + Double.pi
                } else {
                    self.angle = angleOfArctan
                }
            }
        } else {
            self.angle = 0
        }
    }
}
