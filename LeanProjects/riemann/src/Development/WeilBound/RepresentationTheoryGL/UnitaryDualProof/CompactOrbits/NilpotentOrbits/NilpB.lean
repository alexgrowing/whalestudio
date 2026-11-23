import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.CompactOrbits.NilpotentOrbits.NilpotentHypotheses.Assembly
import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.CompactOrbits.NilpotentOrbits.FourierTransforms.FourP
import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.CompactOrbits.NilpotentOrbits.BaseOrbits.BasePPf
import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.CompactOrbits.NilpotentOrbits.OrbitIntegrals.OrbP

namespace PositivityTheory.RgUd.T.Nil.Final

theorem nilpB (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [CharZero k] :
    PositivityTheory.RgUd.T.NilpB (k := k) :=
  PositivityTheory.RgUd.T.Nil.Asm.nilpB_of k (PositivityTheory.RgUd.T.Nil.Four.Final.fourP k) (PositivityTheory.RgUd.T.Nil.Orb.Final.orbP k)
    (PositivityTheory.RgUd.T.Nil.Four.Final.locQ k) (PositivityTheory.RgUd.T.Nil.usage₁₀ k)

end PositivityTheory.RgUd.T.Nil.Final
