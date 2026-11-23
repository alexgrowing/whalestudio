import Mathlib
import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.GenericIrreducibility.NormEqOneOfIsUnitarisableU
import Development.WeilBound.CoreStatements.AutomorphicKernels.UnitaryDualGL.TemperedEigenvalueNorms.Centred

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL ValuativeRel

namespace PositivityTheory.Gud.Pf

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem isCentred_of_unitCC {Δ : Segment k} {δ : IrrGL k} (hL : IsLSeg Δ δ.rep)
    (hU : PositivityTheory.RgUd.UOrder.UnitCC δ.rep) : PositivityTheory.UdReth2.IsCentred Δ :=
  fun _ hω z => PositivityTheory.RgUd.UOrder.log_norm_centralChar_u hL hU hω z

end PositivityTheory.Gud.Pf

end
