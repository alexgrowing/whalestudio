package np

func StartHouseDimension() {
	var point = &Point{0,0}
	printPoint(point)

	for i:=0; i < 100; i++ {
		point = nextPoint(point)
		printPoint(point)
	}
}

func nextPoint(p *Point) *Point {
	return &Point {p.x^2-p.y^2 + 1, 2*p.x*p.y + 1}
}

func printPoint(p *Point) {
	println("{",p.x,",",p.y,"}")
}

type Point struct {
	x int
	y int
}