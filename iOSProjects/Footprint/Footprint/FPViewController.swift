//
//  ViewController.swift
//  Footprint
//
//  Created by apple on 2016/9/24.
//  Copyright © 2016年 WhaleStudio. All rights reserved.
//

import UIKit
import MapKit
import WhaleLib

class FPViewController: UIViewController, MKMapViewDelegate, CLLocationManagerDelegate {
    fileprivate var favoriteSpots = [FPFavoriteSpot]()
    
    @IBOutlet weak var mainMap: MKMapView! {
        didSet {
            mainMap.mapType = .standard
            mainMap.delegate = self
            mainMap.isPitchEnabled = false
            mainMap.isRotateEnabled = false
        }
    }
    @IBOutlet weak var gotoMyLocationButton: UIButton!
    @IBOutlet weak var keywordTextField: UITextField!
    
    fileprivate var locationManager : CLLocationManager!

    override func viewDidLoad() {
        super.viewDidLoad()
        // Do any additional setup after loading the view, typically from a nib.
        
        self.registerGestureRecognizer()
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
        
    }
    
    func mapView(_ mapView: MKMapView, didUpdate userLocation: MKUserLocation) {
        printLog("mapView didUpdate UserLocation")
    }
    
    func mapView(_ mapView: MKMapView, viewFor annotation: MKAnnotation) -> MKAnnotationView? {
        if annotation.isKind(of: MKUserLocation.self) {
            return nil
        } else if annotation.isKind(of: FPSpotAnnotation.self) {
            if let spotView = self.mainMap.dequeueReusableAnnotationView(withIdentifier: KEY_OF_FPSpotAnnotationView) {
                spotView.annotation = annotation
                
                return spotView
            } else {
                let customView = MKAnnotationView(annotation: annotation, reuseIdentifier: KEY_OF_FPSpotAnnotationView)
                
                customView.canShowCallout = false
                customView.image = WLUI.drawTextAsImage(text: "🚩", size: CGSize(width: 16, height: 16), fontSize: 14)
                
                return customView
            }
        } else {
            return nil
        }
    }
    
    func mapView(_ mapView: MKMapView, didSelect view: MKAnnotationView) {
        printLog("annotation is selected")
    }
    
    // MARK: - CLLocationManagerDelegate
    func locationManager(_ manager: CLLocationManager, didUpdateLocations locations: [CLLocation]) {
        if let location = locations.first {
            let region = MKCoordinateRegionMake(location.coordinate, MKCoordinateSpanMake(CONST_DEFAULT_MAP_DELTA, CONST_DEFAULT_MAP_DELTA))
            self.mainMap.setRegion(region, animated: true)
            
            self.locationManager.stopUpdatingLocation()
        }
    }
    
    
    // MARK: - GestureRecognizer
    fileprivate func registerGestureRecognizer() {
        let longPress = UILongPressGestureRecognizer(target: self, action: #selector(FPViewController.handleLongPressGesture(_:)))
        self.mainMap.addGestureRecognizer(longPress)
    }
    
    func handleLongPressGesture(_ sender:UILongPressGestureRecognizer) {
        let locationInMapView = sender.location(in:self.mainMap)
        let coordinate = self.mainMap.convert(locationInMapView, toCoordinateFrom:self.mainMap)
        
        self.addFavoriteSpot(coord: coordinate)
    }
    
    // MARK: - Edit FavoriteSpots
    fileprivate func addFavoriteSpot(coord:CLLocationCoordinate2D) {
        let spot = FPFavoriteSpot(coord: coord)
        self.favoriteSpots.append(spot)
        self.mainMap.addAnnotation(FPSpotAnnotation(spot: spot))
    }
    
    // MARK: - IBActions
    @IBAction func btnGotoMyLocation() {
        self.gotoMyLocation()
    }
    
    @IBAction func btnSearch() {
        self.__googleSearch__()
    }
    
    // MARK: - PrivateMethods
    fileprivate func gotoMyLocation() {
        if self.locationManager == nil {
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
            self.locationManager.distanceFilter = 10
            self.locationManager.delegate = self
            self.locationManager.requestWhenInUseAuthorization()
        }
        
        self.locationManager.startUpdatingLocation()
    }
    
    fileprivate func __googleSearch__() {
        // let url = URL(string: "https://maps.googleapis.com/maps/api/geocode/json?address=1600+Amphitheatre+Parkway,+Mountain+View,+CA&key=AIzaSyDY7yfkjDzsZZkkCjwrkR9XNcE8egqLmzM")
        
        let url = URL(string: "https://maps.googleapis.com/maps/api/geocode/json?key=AIzaSyDY7yfkjDzsZZkkCjwrkR9XNcE8egqLmzM&latlng=40.714224,-78.961452")
        let req = URLRequest(url: url!)
        NSURLConnection.sendAsynchronousRequest(req, queue: OperationQueue.main) { (res, data, error) in
            let ob = try? JSONSerialization.jsonObject(with: data!, options: JSONSerialization.ReadingOptions.mutableContainers) as? [String:AnyObject]
            
            printLog(ob)
        }
    }
    
    fileprivate func __hotSearch__() {
        guard self.keywordTextField.text != nil else {
            return
        }

        let request = MKLocalSearchRequest()
        request.naturalLanguageQuery = self.keywordTextField.text
        request.region = self.mainMap.region
        
        let search = MKLocalSearch(request: request)
        search.start { (res, error) in
            if error == nil {
                for item in (res?.mapItems)! {
                    let mark = item.placemark
                    
                    let region = MKCoordinateRegionMake(mark.location!.coordinate, MKCoordinateSpanMake(CONST_DEFAULT_MAP_DELTA, CONST_DEFAULT_MAP_DELTA))
                    self.mainMap.setRegion(region, animated: true)
                    
                    let anno = MKPointAnnotation()
                    anno.coordinate = mark.location!.coordinate
                    self.mainMap.addAnnotation(anno)
                }
            } else {
                printLog("没搜到啊没搜到")
            }
        }
    }
    
    fileprivate func __keywordSearch__() {
        let geocode = CLGeocoder()
        geocode.geocodeAddressString("东大门") { (placemarks, error) in
            if error == nil {
                for mark in placemarks! {
                    printLog("location:\(String(describing: mark.location));name:\(String(describing: mark.name));country:\(String(describing: mark.country))")
                    let region = MKCoordinateRegionMake(mark.location!.coordinate, MKCoordinateSpanMake(CONST_DEFAULT_MAP_DELTA, CONST_DEFAULT_MAP_DELTA))
                    self.mainMap.setRegion(region, animated: true)
                    
                    let anno = MKPointAnnotation()
                    anno.coordinate = mark.location!.coordinate
                    self.mainMap.addAnnotation(anno)
                }
            } else {
                printLog("解析失败")
            }
        }
    }
}

