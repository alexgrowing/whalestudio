//
//  FPAnnotations.swift
//  Footprint
//
//  Created by alex on 2017/5/9.
//  Copyright © 2017年 WhaleStudio. All rights reserved.
//

import Foundation
import MapKit

let KEY_OF_FPSpotAnnotationView = "FPSpotAnnotationView"

class FPSpotAnnotation : NSObject, MKAnnotation {
    fileprivate let spot:FPFavoriteSpot
    
    init(spot:FPFavoriteSpot) {
        self.spot = spot
        
        super.init()
    }
    
    var coordinate: CLLocationCoordinate2D {
        return self.spot.location
    }
}

class FPSpotsAnnotation: NSObject, MKAnnotation {
    fileprivate let centerOfSpots:CLLocationCoordinate2D
    fileprivate let countsOfSpots:Int
    
    init(centerOfSpots:CLLocationCoordinate2D, countsOfSpots:Int) {
        self.centerOfSpots = centerOfSpots
        self.countsOfSpots = countsOfSpots
        
        super.init()
    }
    
    var coordinate: CLLocationCoordinate2D {
        return self.centerOfSpots
    }
}
