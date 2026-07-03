package surf

// LabelVector LabelVector
type LabelVector struct {
	labels []uint8
}

func newLabelVector(cap uint64) *LabelVector {
	return &LabelVector{
		labels: make([]uint8, 0, cap),
	}
}

func (me *LabelVector) appendLabel(label uint8) {
	me.labels = append(me.labels, label)
}

func (me *LabelVector) labelByIndex(index uint64) uint8 {
	return me.labels[index]
}

func (me *LabelVector) countOfLabels() uint64 {
	return uint64(len(me.labels))
}

func (me *LabelVector) memorySize() uint64 {
	return me.countOfLabels()
}
