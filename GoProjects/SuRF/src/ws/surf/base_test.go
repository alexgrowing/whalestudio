package surf

import (
	"testing"
)

func TestUInt256Mark1(t *testing.T) {
	uint256 := make([]uint64, 4)
	uint256Mark1(uint256, 0)
	uint256Mark1(uint256, 1)
	uint256Mark1(uint256, 33)
	uint256Mark1(uint256, 63)
	uint256Mark1(uint256, 64)
	uint256Mark1(uint256, 255)

	for i, u := range uint256 {
		if i == 0 {
			assertEquals(t, u, 1<<63|1<<62|1<<30|1<<0)
		} else if i == 1 {
			assertEquals(t, u, 1<<63)
		} else if i == 2 {
			assertEquals(t, u, 0)
		} else {
			assertEquals(t, u, 1)
		}
	}
}

func TestUInt256IndexOfNode(t *testing.T) {
	uint256 := make([]uint64, 4)
	uint256Mark1(uint256, 0)
	uint256Mark1(uint256, 1)
	uint256Mark1(uint256, 33)
	uint256Mark1(uint256, 63)
	uint256Mark1(uint256, 64)
	uint256Mark1(uint256, 255)

	assertEquals(t, 0, uint64(uint256IndexOfNode(uint256, 0)))
	assertEquals(t, 1, uint64(uint256IndexOfNode(uint256, 1)))
	assertEquals(t, 3, uint64(uint256IndexOfNode(uint256, 62)))
	assertEquals(t, 3, uint64(uint256IndexOfNode(uint256, 63)))
	assertEquals(t, 4, uint64(uint256IndexOfNode(uint256, 64)))
	assertEquals(t, 5, uint64(uint256IndexOfNode(uint256, 65)))
	assertEquals(t, 5, uint64(uint256IndexOfNode(uint256, 254)))
	assertEquals(t, 5, uint64(uint256IndexOfNode(uint256, 255)))
}

func TestUInt256IsMarked(t *testing.T) {
	uint256 := make([]uint64, 4)
	uint256Mark1(uint256, 0)
	uint256Mark1(uint256, 1)
	uint256Mark1(uint256, 33)
	uint256Mark1(uint256, 63)
	uint256Mark1(uint256, 64)
	uint256Mark1(uint256, 255)

	assertTrue(t, uint256IsMarked(uint256, 0))
	assertTrue(t, uint256IsMarked(uint256, 1))
	assertTrue(t, !uint256IsMarked(uint256, 2))
	assertTrue(t, uint256IsMarked(uint256, 33))
	assertTrue(t, !uint256IsMarked(uint256, 34))
	assertTrue(t, !uint256IsMarked(uint256, 62))
	assertTrue(t, uint256IsMarked(uint256, 63))
	assertTrue(t, uint256IsMarked(uint256, 64))
	assertTrue(t, !uint256IsMarked(uint256, 65))
	assertTrue(t, !uint256IsMarked(uint256, 75))
	assertTrue(t, !uint256IsMarked(uint256, 85))
	assertTrue(t, !uint256IsMarked(uint256, 95))
	assertTrue(t, !uint256IsMarked(uint256, 195))
	assertTrue(t, !uint256IsMarked(uint256, 200))
	assertTrue(t, !uint256IsMarked(uint256, 253))
	assertTrue(t, !uint256IsMarked(uint256, 254))
	assertTrue(t, uint256IsMarked(uint256, 255))

	var found, pos = uint256PosOf1(uint256, 0)
	assertTrue(t, found)
	assertTrue(t, pos == 0)

	found, pos = uint256PosOf1(uint256, 1)
	assertTrue(t, found)
	assertTrue(t, pos == 1)

	found, pos = uint256PosOf1(uint256, 2)
	assertTrue(t, found)
	assertTrue(t, pos == 33)

	found, pos = uint256PosOf1(uint256, 3)
	assertTrue(t, found)
	assertTrue(t, pos == 63)

	found, pos = uint256PosOf1(uint256, 4)
	assertTrue(t, found)
	assertTrue(t, pos == 64)

	found, pos = uint256PosOf1(uint256, 5)
	assertTrue(t, found)
	assertTrue(t, pos == 255)

	found, pos = uint256PosOf1(uint256, 6)
	assertTrue(t, !found)
	assertTrue(t, pos == 0)
}

func TestUint64Mark1(t *testing.T) {
	bits := []uint64{0, 0}
	uint64Mark1(bits, 15)
	uint64Mark1(bits, 64)
	assertTrue(t, !uint64IsMarked(bits, 0))
	assertTrue(t, uint64IsMarked(bits, 15))
	assertTrue(t, !uint64IsMarked(bits, 14))
	assertTrue(t, !uint64IsMarked(bits, 63))
	assertTrue(t, uint64IsMarked(bits, 64))
	assertTrue(t, !uint64IsMarked(bits, 65))
}

func TestUint256OnePositions(t *testing.T) {
	uint256 := make([]uint64, 4)
	uint256Mark1(uint256, 0)
	uint256Mark1(uint256, 1)
	uint256Mark1(uint256, 33)
	uint256Mark1(uint256, 63)
	uint256Mark1(uint256, 64)
	uint256Mark1(uint256, 78)
	uint256Mark1(uint256, 255)

	res := Uint256OnePositions(uint256)
	resShouldBe := []uint8{0, 1, 33, 63, 64, 78, 255}
	for i := range res {
		assertEqualsUint8(t, res[i], resShouldBe[i])
	}
}

func TestSelect1(t *testing.T) {
	uint256 := make([]uint64, 4)
	uint256Mark1(uint256, 0)
	uint256Mark1(uint256, 1)
	uint256Mark1(uint256, 33)
	uint256Mark1(uint256, 63)
	uint256Mark1(uint256, 64)
	uint256Mark1(uint256, 78)
	uint256Mark1(uint256, 255)
	uint256Mark1(uint256, 79)

	assertEquals(t, select1(uint256, 0), 0)
	assertEquals(t, select1(uint256, 1), 1)
	assertEquals(t, select1(uint256, 2), 33)
	assertEquals(t, select1(uint256, 3), 63)
	assertEquals(t, select1(uint256, 4), 64)
	assertEquals(t, select1(uint256, 5), 78)
	assertEquals(t, select1(uint256, 6), 79)
	assertEquals(t, select1(uint256, 7), 255)
}
