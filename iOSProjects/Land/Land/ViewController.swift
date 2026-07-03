//
//  ViewController.swift
//  Land
//
//  Created by apple on 15/12/7.
//  Copyright © 2015年 G & B. All rights reserved.
//

import UIKit
import MapKit
import HealthKit

private let DEFAULTS_FOOTPRINTS = "defaults_footprints"
private let DEFAULTS_LASTDATEANDSTEP = "defaults_last_date_and_step"

private let DEFAULTS_KEY_LATITUDE = "LATITUDE"
private let DEFAULTS_KEY_LONGITUDE = "LONGITUDE"
private let DEFAULTS_KEY_YEAR = "YEAR"
private let DEFAULTS_KEY_MONTH = "MONTH"
private let DEFAULTS_KEY_DAY = "DAY"
private let DEFAULTS_KEY_STEP = "STEP"

class ViewController: UIViewController, MKMapViewDelegate {

    @IBOutlet weak var map: MKMapView! {
        didSet {
            map.mapType = .Standard
            map.delegate = self
            map.showsUserLocation = true
            map.pitchEnabled = false
            map.rotateEnabled = false
        }
    }
    @IBOutlet weak var updateLocationButton: UIButton!
    @IBOutlet weak var statusLabel: UILabel!
    @IBOutlet weak var stepInfoLabel: UILabel!
    
    private var healthKitStore:HKHealthStore!
    private var locationManager : CLLocationManager!
    private var currentTerritories = Set<Territory>()
    private var myFootprints : Set<Footprint>!
    private var myLocationInitialized = false
    private var driveModel = false {
        didSet {
            let textOfUpdateLocationButton:String
            if self.driveModel {
                UIApplication.sharedApplication().idleTimerDisabled = true
                textOfUpdateLocationButton = "行进模式"
            } else {
                UIApplication.sharedApplication().idleTimerDisabled = false
                textOfUpdateLocationButton = "离开"
            }
            
            self.updateLocationButton.setTitle(textOfUpdateLocationButton, forState: .Normal)
        }
    }
    private var setDriveModelTrueAfterRegionDidChanged = false
    
    override func viewDidLoad() {
        super.viewDidLoad()
        // Do any additional setup after loading the view, typically from a nib.
        
        switch CLLocationManager.authorizationStatus() {
        case .AuthorizedAlways:
            print("authorized always")
        case .AuthorizedWhenInUse:
            print("authorized in use")
        case .Denied:
            print("auth denied")
        case .NotDetermined:
            print("auth not determined")
        case .Restricted:
            print("auth restricted")
        }
        
        self.locationManager = CLLocationManager()
        self.locationManager.desiredAccuracy = kCLLocationAccuracyBest
        self.locationManager.requestWhenInUseAuthorization()
        
        self.myFootprints = self.readFootprintsFromDefaults()
        for footprint in self.myFootprints {
            self.addTerritory2Map(footprint.territory)
        }
        
        if HKHealthStore.isHealthDataAvailable() {
            self.healthKitStore = HKHealthStore()
            let healthKitTypesToRead:Set<HKObjectType> = [HKQuantityType.quantityTypeForIdentifier(HKQuantityTypeIdentifierStepCount)!]
            self.healthKitStore.requestAuthorizationToShareTypes(nil, readTypes: healthKitTypesToRead) { (success, error) -> Void in
                if success {
                    
                }
            }
        }
    }

    override func didReceiveMemoryWarning() {
        super.didReceiveMemoryWarning()
        // Dispose of any resources that can be recreated.
    }
    
    // MARK: MKMapViewDelegate
    func mapView(mapView: MKMapView, didFailToLocateUserWithError error: NSError) {
        print(error)
    }
    
    func mapViewWillStartLocatingUser(mapView: MKMapView) {
        print("开始定位")
    }
    
    func mapViewDidStopLocatingUser(mapView: MKMapView) {
        print("停止定位")
    }
    
    func mapView(mapView: MKMapView, didUpdateUserLocation userLocation: MKUserLocation) {
        if !self.myLocationInitialized || self.driveModel {
            self.gotoMyLocation()
            self.myLocationInitialized = true
        }
        
        let footprint = calculateFootprintByLocation(userLocation.coordinate)
        self.try2AddNewFootprint(footprint)
        
        self.modifyStatus("footprint.count:\(self.myFootprints.count)")
    }
    
    func mapView(mapView: MKMapView, rendererForOverlay overlay: MKOverlay) -> MKOverlayRenderer {
        if let longitudeLine = overlay as? LongitudePolyLine {
            let renderer = MKPolylineRenderer(overlay: longitudeLine.line)
            renderer.strokeColor = UIColor.redColor()
            renderer.lineWidth = 1
            
            return renderer
        }
        if let latitudeLine = overlay as? LatitudePolyLine {
            let renderer = MKPolylineRenderer(overlay: latitudeLine.line)
            renderer.strokeColor = UIColor.greenColor()
            renderer.lineWidth = 1
            
            return renderer
        }
        if let ter = overlay as? Territory {
            let renderer = MKPolygonRenderer(overlay: ter.asPolygon)
            renderer.strokeColor = UIColor.yellowColor()
            renderer.lineWidth = 1
            
            var inMyPrints = false
            for myFootprint in self.myFootprints {
                if myFootprint.latitude100 == ter.latitude100 && myFootprint.longitude100 == ter.longitude100 {
                    inMyPrints = true
                }
            }
            
            if inMyPrints {
                renderer.fillColor = UIColor.redColor().colorWithAlphaComponent(0.3)
            } else {
                renderer.fillColor = UIColor.grayColor().colorWithAlphaComponent(0.3)
            }
            
            return renderer
        }
        
        return MKOverlayRenderer()
    }
    
    func mapView(mapView: MKMapView, regionWillChangeAnimated animated: Bool) {
        self.driveModel = false
    }
    
    func mapView(mapView: MKMapView, regionDidChangeAnimated animated: Bool) {
        if self.setDriveModelTrueAfterRegionDidChanged {
            self.driveModel = true
            self.setDriveModelTrueAfterRegionDidChanged = false
        }
        
        let center = mapView.region.center
        let span = mapView.region.span
        
        if span.longitudeDelta >= 0.1 {
            return
        }
        
        let topLatitude4Spot100 = Int((center.latitude - span.latitudeDelta / 2) * 100)
        let bottomLatitude4Spot100 = Int((center.latitude + span.latitudeDelta / 2) * 100)
        let leftLongitude4Spot100 = Int((center.longitude - span.longitudeDelta / 2) * 100)
        let rightLongitude4Spot100 = Int((center.longitude + span.longitudeDelta / 2) * 100)
        
        for var latitude100 = topLatitude4Spot100; latitude100 <= bottomLatitude4Spot100; ++latitude100 {
            
            for var longitude100 = leftLongitude4Spot100; longitude100 <= rightLongitude4Spot100; ++longitude100 {
                let realLongitude100:Int
                if longitude100 >= 18000 {
                    realLongitude100 = longitude100 - 36000
                } else if longitude100 < -18000 {
                    realLongitude100 = longitude100 + 36000
                } else {
                    realLongitude100 = longitude100
                }
                
                let newTerritory = Territory(latitude100: latitude100, longitude100: realLongitude100)
                if !self.currentTerritories.contains(newTerritory) {
                    self.addTerritory2Map(newTerritory)
                }
            }
        }
    }
    
    // MARK: Private Methods
    @IBAction func gotoMyLocation() {
        let userCoordinate = self.map.userLocation.coordinate
        if !validateCoordinate(userCoordinate) {
            return
        }
        
        self.setDriveModelTrueAfterRegionDidChanged = true
        
        let currentRegion = self.map.region
        let currentCenter = currentRegion.center
        let currentSpan = currentRegion.span
        
        let latitudeDelta = abs(currentCenter.latitude-userCoordinate.latitude)
        let longitudeDelta = abs(currentCenter.longitude-userCoordinate.longitude)
        if latitudeDelta < currentSpan.latitudeDelta/2 && longitudeDelta < currentSpan.longitudeDelta/2 {
            // 经度和纬度都在视图范围内
            self.map.setRegion(MKCoordinateRegionMake(userCoordinate, MKCoordinateSpan(latitudeDelta: 0.02, longitudeDelta: 0.02)), animated: true)
        }
        else {
            // 经度或纬度在视图范围外
            let globalRegion = MKCoordinateRegionMake(userCoordinate, MKCoordinateSpan(latitudeDelta: min(max(latitudeDelta, longitudeDelta)*2.2, 160), longitudeDelta: min(max(latitudeDelta, longitudeDelta)*2.2, 360)))
            
            self.map.setRegion(globalRegion, animated: true)
            // 如果setRegion:animated还能加一个complete参数就好了
            NSTimer.scheduledTimerWithTimeInterval(1, target: self, selector: "gotoMyLocation", userInfo: nil, repeats: false)
        }
        
        self.readStepAndRefreshInfoLabel()
        
        self.driveModel = true
    }
    
    @IBAction func toggleDriveModel() {
        self.driveModel = !self.driveModel
    }
    
    private func try2AddNewFootprint(footprint : Footprint) {
        if !self.myFootprints.contains(footprint) {
            self.myFootprints.insert(footprint)
            
            let territoryOfFootprint = footprint.territory
            if self.currentTerritories.contains(territoryOfFootprint) {
                self.refreshTerritory(territoryOfFootprint)
            }
            
            self.writeFootprintsToDefaults(self.myFootprints)
        }
    }
    
    private func modifyStatus(message:String) {
        let formatter = NSDateFormatter()
        formatter.dateFormat = "HH:mm:ss"
        self.statusLabel.text = "\(formatter.stringFromDate(NSDate())):\(message)"
    }
    
    private func addTerritory2Map(territory:Territory) {
        if !self.currentTerritories.contains(territory) {
            self.currentTerritories.insert(territory)
            self.map.addOverlay(territory)
            //                    self.map.addAnnotation(LLPoint(latitude100: latitude100, longitude100: realLongitude100))
        }
    }
    
    private func refreshTerritory(territory:Territory) {
        // alex:没有repaint之类的方法吗?只能移除现有的overlayInMap再重新加一遍吗?
        for overlayInMap in self.map.overlays {
            if let territoryInMap = overlayInMap as? Territory {
                if territoryInMap.latitude100 == territory.latitude100 && territoryInMap.longitude100 == territory.longitude100 {
                    self.map.removeOverlay(territoryInMap)
                    break
                }
            }
        }
        
        self.map.addOverlay(territory)
    }
    
    private func readStepAndRefreshInfoLabel() {
        self.readStepsOfToday { (dateAndStep, error) -> Void in
            if error != nil {
                return
            }
            
            let delta:Int
            if let last = self.readDateAndStepFromDefaults() {
                var savedStepOfToday = 0
                if last.year == dateAndStep.year && last.month == dateAndStep.month && last.day == dateAndStep.day {
                    savedStepOfToday = last.step!
                }
                
                delta = max(dateAndStep.step - savedStepOfToday, 0)
            } else {
                delta = max(dateAndStep.step, 0)
            }
            
            self.writeDateAndStepToDefaults(dateAndStep)
            
            dispatch_async(dispatch_get_main_queue(), {
                self.stepInfoLabel.text = "今日总步数:\(dateAndStep.step);新增:\(delta)"
            })
        }
    }
    
    private func readStepsOfToday(callback:(dateAndStep:DateAndStep, error:ErrorType?) -> Void) {
        let calendar = NSCalendar.currentCalendar()
        let now = NSDate()
        
        let components = calendar.components(NSCalendarUnit.Year.union(.Month).union(.Day), fromDate: now)
        
        let startDate = calendar.dateFromComponents(components)
        let endDate = calendar.dateByAddingUnit(NSCalendarUnit.Day, value: 1, toDate: startDate!, options: NSCalendarOptions(rawValue: 0))
        
        let sampleType = HKSampleType.quantityTypeForIdentifier(HKQuantityTypeIdentifierStepCount)
        let predicate = HKQuery.predicateForSamplesWithStartDate(startDate, endDate: endDate, options: .None)
        
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
                        let steps = Int(quantity.quantity.doubleValueForUnit(HKUnit.countUnit()))
                        if let stepOfSource = datas[quantity.source] {
                            datas[quantity.source] = stepOfSource + steps
                        } else {
                            datas[quantity.source] = steps
                        }
                    }
                }
            }
            
            var maxStep = 0
            for (_, step) in datas {
                maxStep = max(maxStep, step)
            }
            
            callback(dateAndStep: DateAndStep(step: maxStep, year: components.year, month: components.month, day: components.day), error: error)
        }
        
        self.healthKitStore.executeQuery(query)
    }
    
    // MARK: UserDefaults
    private func readFootprintsFromDefaults() -> Set<Footprint> {
        var savedPrints = Set<Footprint>()
        if let unarchivedObjects = NSUserDefaults.standardUserDefaults().objectForKey(DEFAULTS_FOOTPRINTS) as? [NSData] {
            for ob in unarchivedObjects {
                if let footprint = NSKeyedUnarchiver.unarchiveObjectWithData(ob) as? Footprint {
                    savedPrints.insert(footprint)
                }
            }
        }
        
        return savedPrints
    }
    
    private func writeFootprintsToDefaults(prints:Set<Footprint>) {
        let datas = prints.map {
            return NSKeyedArchiver.archivedDataWithRootObject($0)
        }
        
        let defaults = NSUserDefaults.standardUserDefaults()
        defaults.setObject(datas, forKey: DEFAULTS_FOOTPRINTS)
        
        defaults.synchronize()
    }
    
    private func readDateAndStepFromDefaults() -> DateAndStep? {
        if let ob = NSUserDefaults.standardUserDefaults().objectForKey(DEFAULTS_LASTDATEANDSTEP) as? NSData {
            if let ds = NSKeyedUnarchiver.unarchiveObjectWithData(ob) as? DateAndStep {
                return ds
            }
        }
        
        return nil
    }
    
    private func writeDateAndStepToDefaults(ds:DateAndStep) {
        let defaults = NSUserDefaults.standardUserDefaults()
        defaults.setObject(NSKeyedArchiver.archivedDataWithRootObject(ds), forKey: DEFAULTS_LASTDATEANDSTEP)
        defaults.synchronize()
    }
}

//func asRealLongitude(longitude:Double) -> Double {
//    return (longitude + 180 + 360) % 360 - 180
//}

private func calculateFootprintByLocation(coordinate: CLLocationCoordinate2D) -> Footprint {
    let todayComponents = NSCalendar.currentCalendar().components(NSCalendarUnit.Year.union(NSCalendarUnit.Month).union(NSCalendarUnit.Day), fromDate: NSDate())
    return Footprint(
        latitude100: Int(coordinate.latitude * 100),
        longitude100: Int(coordinate.longitude * 100),
        year: todayComponents.year,
        month: todayComponents.month,
        day: todayComponents.day)
}

private func validateCoordinate(coordinate:CLLocationCoordinate2D) -> Bool {
    return coordinate.latitude >= -90 && coordinate.latitude <= 90 && coordinate.longitude >= -180 && coordinate.longitude <= 180
}

class Territory : NSObject, MKOverlay {
    private let latitude100:Int
    private let longitude100:Int
    
    init(latitude100:Int, longitude100:Int) {
        self.latitude100 = latitude100
        self.longitude100 = longitude100
    }
    
    var coordinate:CLLocationCoordinate2D {
        return self.asPolygon.coordinate
    }
    
    var boundingMapRect:MKMapRect {
        return self.asPolygon.boundingMapRect
    }
    
    var asPolygon:MKPolygon {
        let smallLatitude100 = self.latitude100
        let largeLatitude100 = self.latitude100>=0 ? self.latitude100+1 : self.latitude100-1
        let smallLongitude100:Int
        // longitude100如果是18000或是-18000怎么办？
        if self.longitude100 == 18000 || self.longitude100 == -18000 {
            smallLongitude100 = 17999
        } else if self.longitude100 > 18000 {
            smallLongitude100 = self.longitude100 - 36000
        } else {
            smallLongitude100 = self.longitude100
        }
        let largeLongitude100 = smallLongitude100>=0 ? smallLongitude100+1 : smallLongitude100-1
        
        var points = [
            CLLocationCoordinate2DMake(Double(smallLatitude100) / 100, Double(smallLongitude100) / 100),
            CLLocationCoordinate2DMake(Double(smallLatitude100) / 100, Double(largeLongitude100) / 100),
            CLLocationCoordinate2DMake(Double(largeLatitude100) / 100, Double(largeLongitude100) / 100),
            CLLocationCoordinate2DMake(Double(largeLatitude100) / 100, Double(smallLongitude100) / 100)
        ]
        return MKPolygon(coordinates: &points, count: points.count)
    }
    
    // MARK: NSObjectProtocol.Hashable
    override var hash:Int {
        return self.latitude100*3 + self.longitude100*7
    }
    
    override func isEqual(object: AnyObject?) -> Bool {
        if let ter = object as? Territory {
            return self.latitude100 == ter.latitude100 && self.longitude100 == ter.longitude100
        }
        
        return false
    }
}

class LLPoint : NSObject, MKAnnotation {
    private let latitude100:Int
    private let longitude100:Int
    
    init(latitude100:Int, longitude100:Int) {
        self.latitude100 = latitude100
        self.longitude100 = longitude100
    }
    
    var coordinate:CLLocationCoordinate2D {
        return CLLocationCoordinate2D(latitude: Double(self.latitude100)/100, longitude: Double(self.longitude100)/100)
    }
    
    var title: String? {
        return "[\(self.latitude100),\(self.longitude100)]"
    }
}

class Footprint : NSObject, NSCoding {
    private var latitude100:Int!
    private var longitude100:Int!
    private var year:Int!
    private var month:Int!
    private var day:Int!
    
    init(latitude100:Int, longitude100:Int, year:Int, month:Int, day:Int) {
        self.latitude100 = latitude100
        self.longitude100 = longitude100
        self.year = year
        self.month = month
        self.day = day
    }
    
    override var description : String {
        get {
            return "\(self.year)-\(self.month)-\(self.day):[\(self.latitude100),\(self.longitude100)]"
        }
    }
    
    // MARK: NSCoding
    func encodeWithCoder(aCoder: NSCoder) {
        aCoder.encodeInteger(self.latitude100, forKey: DEFAULTS_KEY_LATITUDE)
        aCoder.encodeInteger(self.longitude100, forKey: DEFAULTS_KEY_LONGITUDE)
        aCoder.encodeInteger(self.year, forKey: DEFAULTS_KEY_YEAR)
        aCoder.encodeInteger(self.month, forKey: DEFAULTS_KEY_MONTH)
        aCoder.encodeInteger(self.day, forKey: DEFAULTS_KEY_DAY)
    }
    
    required init(coder aDecoder: NSCoder) {
        self.latitude100 = aDecoder.decodeIntegerForKey(DEFAULTS_KEY_LATITUDE)
        self.longitude100 = aDecoder.decodeIntegerForKey(DEFAULTS_KEY_LONGITUDE)
        self.year = aDecoder.decodeIntegerForKey(DEFAULTS_KEY_YEAR)
        self.month = aDecoder.decodeIntegerForKey(DEFAULTS_KEY_MONTH)
        self.day = aDecoder.decodeIntegerForKey(DEFAULTS_KEY_DAY)
    }
    
    // MARK: NSObjectProtocol.Hashable
    override var hash : Int {
        return self.latitude100*3 + self.longitude100*7 + self.year*11 + self.month*13 + self.day*17
    }
    
    override func isEqual(object: AnyObject?) -> Bool {
        if let otherPrint = object as? Footprint {
            return self.latitude100 == otherPrint.latitude100 && self.longitude100 == otherPrint.longitude100 && self.year == otherPrint.year && self.month == otherPrint.month && self.day == otherPrint.day
        }
        
        return false
    }
    
    // MARK: Private Method
    private var territory : Territory {
        return Territory(latitude100: self.latitude100, longitude100: self.longitude100)
    }
}

class DateAndStep : NSObject, NSCoding {
    private var step:Int!
    private var year:Int!
    private var month:Int!
    private var day:Int!
    
    init(step:Int, year:Int, month:Int, day:Int) {
        self.step = step
        self.year = year
        self.month = month
        self.day = day
    }
    
    // MARK: NSCoding
    func encodeWithCoder(aCoder: NSCoder) {
        aCoder.encodeInteger(self.step, forKey: DEFAULTS_KEY_STEP)
        aCoder.encodeInteger(self.year, forKey: DEFAULTS_KEY_YEAR)
        aCoder.encodeInteger(self.month, forKey: DEFAULTS_KEY_MONTH)
        aCoder.encodeInteger(self.day, forKey: DEFAULTS_KEY_DAY)
    }
    
    required init?(coder aDecoder: NSCoder) {
        self.step = aDecoder.decodeIntegerForKey(DEFAULTS_KEY_STEP)
        self.year = aDecoder.decodeIntegerForKey(DEFAULTS_KEY_YEAR)
        self.month = aDecoder.decodeIntegerForKey(DEFAULTS_KEY_MONTH)
        self.day = aDecoder.decodeIntegerForKey(DEFAULTS_KEY_DAY)
        
    }
}

class LongitudePolyLine : NSObject, MKOverlay {
    private let line:MKPolyline
    
    init(longitude:Double) {
        var points = [
            CLLocationCoordinate2DMake(90, longitude),
            CLLocationCoordinate2DMake(-90, longitude)
        ]
        self.line = MKPolyline(coordinates: &points, count: points.count)
    }
    
    var coordinate: CLLocationCoordinate2D {
        return self.line.coordinate
    }
    
    var boundingMapRect: MKMapRect {
        return self.line.boundingMapRect
    }
}

class LatitudePolyLine : NSObject, MKOverlay {
    private let line:MKPolyline
    
    init(latitude:Double) {
        var points = [
            CLLocationCoordinate2DMake(latitude, -180),
            CLLocationCoordinate2DMake(latitude, 0),
            CLLocationCoordinate2DMake(latitude, 180)
        ]
        self.line = MKPolyline(coordinates: &points, count: points.count)
    }
    
    var coordinate: CLLocationCoordinate2D {
        return self.line.coordinate
    }
    
    var boundingMapRect: MKMapRect {
        return self.line.boundingMapRect
    }
}
