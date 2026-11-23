import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.CompactOrbits.NilpotentOrbits.FourierTransforms.SuppCongr
import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.CompactOrbits.NilpotentOrbits.FourierTransforms.ContinuousQZ
import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.CompactOrbits.NilpotentOrbits.FourierTransforms.TraceEqZeroOfQZ
import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.CompactOrbits.NilpotentOrbits.FourierTransforms.ReflH

namespace PositivityTheory.RgUd.T.Nil.Four.Final

open PositivityTheory.RgUd.T.Nil

variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem fourP [CharZero k] : FourP (k := k) :=
  PositivityTheory.RgUd.T.Nil.Four.fourP_of PositivityTheory.RgUd.T.Nil.Four.Phi2.phiP PositivityTheory.RgUd.T.Nil.Four.Alg.compP

theorem locQ : LocQ (k := k) := PositivityTheory.RgUd.T.Nil.Four.locQ_pf

end PositivityTheory.RgUd.T.Nil.Four.Final
