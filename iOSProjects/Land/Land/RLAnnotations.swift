//
//  RLAnnotations.swift
//  Land
//
//  Created by apple on 16/2/22.
//  Copyright © 2016年 G & B. All rights reserved.
//

import MapKit
import LandLib

private let COLOR_OF_TERRITORY_VISITED = UIColor.green.withAlphaComponent(0.3)
private let COLOR_OF_TERRITORY_OCCUPIED = UIColor.blue.withAlphaComponent(0.3)

class TerritoryRenderer : MKPolygonRenderer {
    fileprivate let territory:Territory
    
    init(territory:Territory) {
        self.territory = territory
        super.init(polygon: territory.asPolygon)
        
        self.lineWidth = 1
        self.strokeColor = UIColor.gray
    }
    
    /*
     * mapRect标识的范围并不是该Renderer的范围,因为MKMap画地图时每个Scale都把地图拆成一块一块画的,mapRect就是这个一块一块的
     */
    override func draw(_ mapRect: MKMapRect, zoomScale: MKZoomScale, in context: CGContext) {
        if let theUser = RLUser.getCurrentUser() , theUser.readOnlyMyTerritories.contains(self.territory) {
            self.fillColor = COLOR_OF_TERRITORY_OCCUPIED
        } else {
            self.fillColor = COLOR_OF_TERRITORY_VISITED
        }
        
        /*
        let drawRect = self.rectForMapRect(mapRect)
        
        let footprintImage = FOOTPRINT_OF_SIZE_9_IMAGE
        CGContextSaveGState(context)
        CGContextTranslateCTM(context, CGRectGetMinX(drawRect), CGRectGetMinY(drawRect))
        CGContextScaleCTM(context, 1/zoomScale, 1/zoomScale)
        CGContextTranslateCTM(context, footprintImage.size.width, footprintImage.size.height)
        CGContextScaleCTM(context, 1, -1)
        CGContextDrawImage(context, CGRectMake(0, 0, footprintImage.size.width, footprintImage.size.height), footprintImage.CGImage)
        CGContextRestoreGState(context)
        */
        
        super.draw(mapRect, zoomScale: zoomScale, in: context)
    }
}

class TerritoryAnnotation : NSObject, MKAnnotation {
    let territory:Territory
    
    init(territory:Territory) {
        self.territory = territory
    }
    
    var coordinate:CLLocationCoordinate2D {
        let lat = self.territory.latitude100 >= 0 ? Double(self.territory.latitude100 + 1)/100 : Double(self.territory.latitude100)/100
        let lon = self.territory.longitude100 >= 0 ? Double(self.territory.longitude100)/100 : Double(self.territory.longitude100 - 1)/100
        return CLLocationCoordinate2D(latitude: lat, longitude: lon)
    }
    
    var title: String? {
        return self.territory.description
    }
}

/*
class RLUserAnnotationView : MKAnnotationView {
    private var footprintImageView:UIImageView!
    
    override init(frame: CGRect) {
        super.init(frame:frame)
    }
    
    override init(annotation: MKAnnotation?, reuseIdentifier: String?) {
        super.init(annotation: annotation, reuseIdentifier: reuseIdentifier)
        
        let sizeOfImage = FOOTPRINT_OF_SIZE_9_IMAGE.size
        let imageView = UIImageView(frame:CGRectMake(0,0,sizeOfImage.width,sizeOfImage.height))
        imageView.image = FOOTPRINT_OF_SIZE_9_IMAGE
        self.addSubview(imageView)
        
        self.footprintImageView = imageView
    }
    
    func setAngleOfFootprint(angle:CGFloat) {
        self.footprintImageView!.transform = CGAffineTransformMakeRotation(angle)
        self.setNeedsDisplay()
    }

    required init?(coder aDecoder: NSCoder) {
        fatalError("init(coder:) has not been implemented")
    }
}
*/

