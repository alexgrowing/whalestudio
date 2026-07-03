//
//  RLAnnotation.swift
//  LandLib
//
//  Created by apple on 16/2/22.
//  Copyright © 2016年 WhaleStudio. All rights reserved.
//

import MapKit

open class Territory : NSObject, MKOverlay {
    public let latitude100:Int
    public let longitude100:Int
    
    public init(latitude100:Int, longitude100:Int) {
        self.latitude100 = (latitude100 + 9000) % 18000 - 9000
        self.longitude100 = (longitude100 + 18000) % 36000 - 18000
    }
    
    open var coordinate:CLLocationCoordinate2D {
        return self.asPolygon.coordinate
    }
    
    open var boundingMapRect:MKMapRect {
        return self.asPolygon.boundingMapRect
    }
    
    open var asPolygon:MKPolygon {
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
    
    // MARK: - NSObjectProtocol.Hashable
    override open var hash:Int {
        return self.latitude100*3 + self.longitude100*7
    }
    
    override open func isEqual(_ object: Any?) -> Bool {
        if let ter = object as? Territory {
            return self.latitude100 == ter.latitude100 && self.longitude100 == ter.longitude100
        }
        
        return false
    }
    
    // MARK : - Json
    public static func build(_ json:[String:AnyObject]) -> Territory? {
        guard let theLatitude100 = json["la"] as? Int else {return nil}
        guard let theLongitude100 = json["lo"] as? Int else {return nil}
        
        return Territory(latitude100: theLatitude100, longitude100: theLongitude100)
    }
    
    open func asJson() -> [String:Int] {
        return [
            "la":self.latitude100,
            "lo":self.longitude100
        ]
    }
    
    override open var description:String {
        return "(\(self.latitude100),\(self.longitude100))"
    }
    
    static public func decode(_ data:Data) -> Set<Territory> {
        var territories = Set<Territory>()
        
        if let array = (try? JSONSerialization.jsonObject(with: data, options: JSONSerialization.ReadingOptions.mutableContainers)) as? [[String:Int]] {
            for json in array {
                if let theTer = Territory.build(json as [String : AnyObject]) {
                    territories.insert(theTer)
                }
            }
        }
        
        return territories
    }
}
