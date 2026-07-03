//
//  CircleImage.swift
//  Startup4SwiftUI
//
//  Created by alex on 2020/1/10.
//  Copyright © 2020 WhaleStudio. All rights reserved.
//

import SwiftUI

struct CircleImage: View {
    var body: some View {
        Image("demo")
        .resizable()
            .frame(width:200, height:200)
        .clipShape(Circle())
            .overlay(Circle().stroke(Color.white, lineWidth: 4))
        .shadow(radius: 10)
    }
}

struct CircleImage_Previews: PreviewProvider {
    static var previews: some View {
        CircleImage()
    }
}
