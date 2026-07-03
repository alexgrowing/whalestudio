package tools

import (
	"fmt"
	"image"
	"image/color"
	"image/draw"
	"image/jpeg"
	"image/png"
	"math"
	"os"

	"code.google.com/p/graphics-go/graphics"
)

func ImageProcess()  {
	sourceImages := []string{
		"1","2","3","4","5",
	}
	for _, imageIndex := range sourceImages {
		fileSrc, err := os.Open(imageIndex + ".png")
		if err != nil {
			panic(err)
		}
		defer fileSrc.Close()

		imageSrc, err := png.Decode(fileSrc)
		if err != nil {
			panic(err)
		}

		exportFiles(imageIndex, imageSrc, parameters4ScreenShot)
		//exportFiles(imageIndex, imageSrc, parameters4Logo)
	}

	fmt.Printf("ok\n")
}

type Parameters struct {
	suffix string
	width int
	height int
}

func newParameters(s string, w int, h int) *Parameters {
	p := Parameters{}
	p.suffix = s
	p.width = w
	p.height = h

	return &p
}

var parameters4ScreenShot = []*Parameters {
	newParameters("4", 640, 960),
	newParameters("5", 640, 1136),
	newParameters("6", 750, 1334),
	newParameters("6p", 1242, 2208),
	newParameters("iPad", 1536, 2048),
	newParameters("iPadPro", 2048, 2732),
	newParameters("X", 1242, 2688),
}

var parameters4Logo = []*Parameters {
	newParameters("40", 40, 40),
	newParameters("60", 60, 60),
	newParameters("58", 58, 58),
	newParameters("87", 87, 87),
	newParameters("80", 80, 80),
	newParameters("120", 120, 120),
	newParameters("180", 180, 180),
	newParameters("20", 20, 20),
	newParameters("29", 29, 29),
	newParameters("76", 76, 76),
	newParameters("152", 152, 152),
	newParameters("167", 167, 167),
	newParameters("1024", 1024, 1024),

}

func exportFiles(sourceImageName string, imageSrc image.Image, ps []*Parameters) {
	for _, p := range ps {
		fileDst, _ := os.Create(sourceImageName + "_" + p.suffix + ".png")
		defer fileDst.Close()
		export(imageSrc, p.width, p.height, fileDst)
	}
}

func export(imageSrc image.Image, newDx int, newDy int, fileDst *os.File) {
	bounds := imageSrc.Bounds()
	dx := bounds.Dx()
	dy := bounds.Dy()
	xscale := float64(dx) / float64(newDx)
	yscale := float64(dy) / float64(newDy)
	fmt.Println("xscale:", xscale, " yscale:", yscale)
	scale := math.Max(xscale, yscale)
	middleDx := int(float64(dx) / scale)
	middleDy := int(float64(dy) / scale)
	middleBounds := image.Rect(0, 0, middleDx, middleDy)
	middleImage := image.NewRGBA(middleBounds)
	graphics.Scale(middleImage, imageSrc)

	desBounds := image.Rect(0, 0, newDx, newDy)
	imageDst := image.NewRGBA(desBounds)
	white := color.RGBA{255, 255, 255, 255}
	draw.Draw(imageDst, desBounds, &image.Uniform{white}, image.ZP, draw.Src)

	//	draw.Draw(imageDst, middleBounds, middleImage, image.ZP, draw.Src)

	widthDelta := newDx - middleDx
	heightDelta := newDy - middleDy
	draw.Draw(imageDst, image.Rect(widthDelta/2, heightDelta/2, middleDx+widthDelta/2, middleDy+heightDelta/2), middleImage, image.ZP, draw.Src)

	//	newBounds := image.Rect(0, 0, newDx, newDy)
	//	imageDst := image.NewRGBA(newBounds)
	//	white := color.RGBA{255, 255, 255, 255}
	//	draw.Draw(dst, newBounds, &image.Uniform{white}, image.ZP, draw.Src)
	//	graphics.Scale(imageDst, imageSrc)

	//	white := color.RGBA{255, 255, 255, 255}
	//	draw.Draw(dst, newBounds, &image.Uniform{white}, image.ZP, draw.Src)
	//	draw.Draw(dst, newBounds, m1, image.ZP, draw.Src)

	err := png.Encode(fileDst, imageDst)
	if err != nil {
		panic(err)
	}
}

func test() {
	f1, err := os.Open("1.jpg")
	if err != nil {
		panic(err)
	}
	defer f1.Close()

	f2, err := os.Open("2.jpg")
	if err != nil {
		panic(err)
	}
	defer f2.Close()

	f3, err := os.Create("3.jpg")
	if err != nil {
		panic(err)
	}
	defer f3.Close()

	m1, err := jpeg.Decode(f1)
	if err != nil {
		panic(err)
	}
	bounds := m1.Bounds()

	m2, err := jpeg.Decode(f2)
	if err != nil {
		panic(err)
	}

	m := image.NewRGBA(bounds)
	white := color.RGBA{255, 255, 255, 255}
	draw.Draw(m, bounds, &image.Uniform{white}, image.ZP, draw.Src)
	draw.Draw(m, bounds, m1, image.ZP, draw.Src)
	draw.Draw(m, image.Rect(100, 200, 300, 600), m2, image.Pt(250, 60), draw.Src)

	err = jpeg.Encode(f3, m, &jpeg.Options{90})
	if err != nil {
		panic(err)
	}

	fmt.Printf("ok\n")
}