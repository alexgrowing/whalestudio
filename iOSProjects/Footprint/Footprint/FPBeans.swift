//
//  FPBeans.swift
//  Footprint
//
//  Created by alex on 2017/5/10.
//  Copyright © 2017年 WhaleStudio. All rights reserved.
//

import Foundation
import MapKit

class FPFavoriteSpot : NSObject {
    fileprivate let coordinate:CLLocationCoordinate2D
    
    init(coord:CLLocationCoordinate2D) {
        self.coordinate = coord
        
        super.init()
    }
    
    var location:CLLocationCoordinate2D {
        return self.coordinate
    }
    
    override var description: String {
        return "\(self.coordinate)"
    }
}
