import Development.WeilBound.RepresentationTheoryGL.TubeMeasures.DisjointTubes.ProductMapEquality.PiCdEqMap
import Development.WeilBound.RepresentationTheoryGL.TubeMeasures.DisjointTubes.LevelStabilisers.MemStabOfLev
import Development.WeilBound.RepresentationTheoryGL.TubeMeasures.DisjointTubes.UpperFactors.FactorUpper
import Development.WeilBound.RepresentationTheoryGL.TubeMeasures.DisjointTubes.InverseMultiplication.IsKMInvMul
import Development.WeilBound.RepresentationTheoryGL.TubeMeasures.DisjointTubes.ExponentialThreeBound.LeExpThree
import Development.WeilBound.RepresentationTheoryGL.TubeMeasures.DisjointTubes.BoxExistence.ExistsBox
import Development.WeilBound.RepresentationTheoryGL.TubeMeasures.DisjointTubes.MeasureSumBounds.SumMuFLe
import Development.WeilBound.RepresentationTheoryGL.TubeMeasures.DisjointTubes.FormalDegreeRankTwo.FinrankEqTwoFdeg
import Development.WeilBound.RepresentationTheoryGL.TubeMeasures.DisjointTubes.ConstantSupremum.Tube0

namespace MainStatements.Tam.Plug

theorem up : UpSt := MainStatements.Tam.up MainStatements.Tam.vol MainStatements.Tam.stab MainStatements.Tam.num

theorem low : LowSt := MainStatements.Tam.low MainStatements.Tam.vol MainStatements.Tam.stab MainStatements.Tam.num

theorem comp : CompSt := MainStatements.Tam.comp (tube0 MainStatements.Tam.vol MainStatements.Tam.stab MainStatements.Tam.idx) MainStatements.Tam.num

theorem size : SizeSt := MainStatements.Tam.size

end MainStatements.Tam.Plug
