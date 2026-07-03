//
//  FPCalculates.swift
//  Footprint
//
//  Created by alex on 2017/5/10.
//  Copyright © 2017年 WhaleStudio. All rights reserved.
//

import Foundation
import WhaleLib
import MapKit

class FPCalculates {
    static func calculateBorderOfRegion(region:MKCoordinateRegion) -> (top:CLLocationDegrees, bottom:CLLocationDegrees, left:CLLocationDegrees, right:CLLocationDegrees) {
        let centerOfRegion = region.center
        let spanOfRegion = region.span

        return (
            centerOfRegion.latitude + spanOfRegion.latitudeDelta/2,
            centerOfRegion.latitude - spanOfRegion.latitudeDelta/2,
            FPCalculates.__ensureLongitudeBetween0To360__(longitude: centerOfRegion.longitude + 180 - spanOfRegion.longitudeDelta) - 180,
            FPCalculates.__ensureLongitudeBetween0To360__(longitude: centerOfRegion.longitude + 180 + spanOfRegion.longitudeDelta) - 180
        )
    }
    
    fileprivate static func __ensureLongitudeBetween0To360__(longitude:CLLocationDegrees) -> CLLocationDegrees {
        if longitude > 360 {
            return FPCalculates.__ensureLongitudeBetween0To360__(longitude:longitude - 360)
        } else if longitude < 0 {
            return FPCalculates.__ensureLongitudeBetween0To360__(longitude:longitude + 360)
        }
        
        return longitude
    }
    
    static func calculateAnnotations(spots:[FPFavoriteSpot], region:MKCoordinateRegion) -> [MKAnnotation] {
        var ret = [MKAnnotation]()
        for spot in spots {
            ret.append(FPSpotAnnotation(spot: spot))
        }
        
        return ret
        
        /*
        var map = [TwoIntAsHashable:[FPFavoriteSpot]]()
        
        let spanOfBlock = region.span.longitudeDelta / CLLocationDegrees(CONST_DEFAULT_COUNT_OF_BLOCK_EACH_WIDTH)
        for index in 0 ..< spots.count {
            let spot = spots[index]
            
            let indexOfLatitude = Int(spot.location.latitude / spanOfBlock)
            let indexOfLongitude = Int(spot.location.longitude / spanOfBlock)
            
            let tempKey = TwoIntAsHashable(key1: indexOfLatitude, key2: indexOfLongitude)
            
            if !map.keys.contains(tempKey) {
                map.updateValue([FPFavoriteSpot](), forKey: tempKey)
            }
            
            map[tempKey]!.append(spot)
        }
        
        var ret = [MKAnnotation]()
        for (_, spots) in map {
            let firstSpot = spots.first!
            
            ret.append(FPSpotsAnnotation(
                centerOfSpots: firstSpot.location, countsOfSpots: spots.count)
            )
        }
        
        return ret
 */
    }
}

class TwoIntAsHashable:Hashable {
    fileprivate let k1:Int
    fileprivate let k2:Int
    
    init(key1:Int, key2:Int) {
        self.k1 = key1
        self.k2 = key2
    }
    
    var hashValue: Int {
        return self.k1 * 3 + self.k2 * 7 + 11
    }
    
    var description: String {
        return "(\(self.k1),\(self.k2))"
    }
}

func ==(lhs: TwoIntAsHashable, rhs: TwoIntAsHashable) -> Bool {
    return lhs.k1 == rhs.k1 && lhs.k2 == rhs.k2
}
