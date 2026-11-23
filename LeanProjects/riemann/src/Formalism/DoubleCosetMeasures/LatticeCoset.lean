import Formalism.DoubleCosetMeasures.Statement
import Formalism.DoubleCosetMeasures.LowerUnipotentOrbits.DoubleCosetEqPreimage
import Formalism.DoubleCosetMeasures.LowerUnipotentOrbits.TwoSided
import Formalism.DoubleCosetMeasures.LowerUnipotentOrbits.IsIntOfLatOfLe
import Formalism.DoubleCosetMeasures.LowerUnipotentOrbits.LowUniMulVecELast
import Formalism.DoubleCosetMeasures.LowerUnipotentOrbits.IsOpenIsIntSet
import Formalism.DoubleCosetMeasures.LowerUnipotentOrbits.MulInvBlockDiagApplySameBlock
import Formalism.DoubleCosetMeasures.LowerUnipotentOrbits.ExistsContinuousLowerUpperEntry
import Formalism.DoubleCosetMeasures.LowerUnipotentOrbits.IsClosedLowUni
import Formalism.DoubleCosetMeasures.StatementZ
import Formalism.DoubleCosetMeasures.LowerUnipotentOrbits.LemmaU
import Formalism.DoubleCosetMeasures.StatementV
import Formalism.DoubleCosetMeasures.LowerUnipotentOrbits.RelIndexMulMeasure
import Formalism.DoubleCosetMeasures.LowerUnipotentOrbits.MeasureUniformizerMatrixSetMulCard

namespace Formalism.DoubleCosetMeasures.Final

open Formalism.DoubleCosetMeasures

theorem intRightInv : Formalism.DoubleCosetMeasures.IntRightInv := Formalism.DoubleCosetMeasures.P.intRightInv
theorem intTwoSided : Formalism.DoubleCosetMeasures.IntTwoSided := Formalism.DoubleCosetMeasures.P.intTwoSided
theorem dosetVol : Formalism.DoubleCosetMeasures.DosetVol := Formalism.DoubleCosetMeasures.P.dosetVol
theorem intBiInv : Formalism.DoubleCosetMeasures.IntBiInv := Formalism.DoubleCosetMeasures.P.intBiInv
theorem uniGroup : Formalism.DoubleCosetMeasures.UniGroup := Formalism.DoubleCosetMeasures.P.uniGroup
theorem simpleAdd : Formalism.DoubleCosetMeasures.SimpleAdd := Formalism.DoubleCosetMeasures.P.simpleAdd
theorem intInv : Formalism.DoubleCosetMeasures.IntInv := Formalism.DoubleCosetMeasures.P.intInv
theorem latticeCoset : Formalism.DoubleCosetMeasures.LatticeCoset := Formalism.DoubleCosetMeasures.P.latticeCoset
theorem isoInv : Formalism.DoubleCosetMeasures.IsoInv := Formalism.DoubleCosetMeasures.P.isoInv
theorem isoFinite : Formalism.DoubleCosetMeasures.IsoFinite := Formalism.DoubleCosetMeasures.P.isoFinite
theorem bbFinite : Formalism.DoubleCosetMeasures.BBFinite := Formalism.DoubleCosetMeasures.P.bbFinite_of intTwoSided intInv isoInv simpleAdd
theorem bbNorm : Formalism.DoubleCosetMeasures.BBNorm := Formalism.DoubleCosetMeasures.P.bbNorm_of bbFinite
theorem phaseWellDef : Formalism.DoubleCosetMeasures.PhaseWellDef := Formalism.DoubleCosetMeasures.P.phaseWellDef
theorem sectionBij : Formalism.DoubleCosetMeasures.SectionBij := Formalism.DoubleCosetMeasures.P.sectionBij
theorem suppCompact : Formalism.DoubleCosetMeasures.SuppCompact := Formalism.DoubleCosetMeasures.P.suppCompact
theorem haarExists : Formalism.DoubleCosetMeasures.HaarExists := Formalism.DoubleCosetMeasures.P.haarExists
theorem suppJ : Formalism.DoubleCosetMeasures.SuppJ := Formalism.DoubleCosetMeasures.P.suppJ
theorem lemmaUSplit : Formalism.DoubleCosetMeasures.LemmaUSplit := Formalism.DoubleCosetMeasures.P.lemmaUSplit
theorem glRed : Formalism.DoubleCosetMeasures.GLRed := Formalism.DoubleCosetMeasures.P.glRed
theorem volJ : Formalism.DoubleCosetMeasures.VolJ := Formalism.DoubleCosetMeasures.P.volJ
theorem volII : Formalism.DoubleCosetMeasures.VolII := Formalism.DoubleCosetMeasures.P.volII
theorem volJadd : Formalism.DoubleCosetMeasures.VolJadd := Formalism.DoubleCosetMeasures.P.volJadd

end Formalism.DoubleCosetMeasures.Final
