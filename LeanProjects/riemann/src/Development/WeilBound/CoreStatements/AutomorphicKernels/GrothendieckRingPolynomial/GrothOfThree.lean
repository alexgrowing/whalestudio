import Mathlib
import Development.WeilBound.CoreStatements.AutomorphicKernels.GrothendieckRingPolynomial.GrothOfCls
import Development.WeilBound.CoreStatements.AutomorphicKernels.GrothendieckRingPolynomial.PeelGood

namespace PositivityTheory.Groth

theorem groth_of_three (hZ : GlobalTheory.Published.SegmentRepresentation)
    (hI : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], Zc.Cos.LUnlinkedIrr k)
    (H : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k],
      PositivityTheory.Exh.MidP k ∧ PositivityTheory.Exh.RefineP k ∧ PositivityTheory.Exh.SwapP k) : GlobalTheory.Published.GrothendieckRingPolynomial :=
  groth_of_cls fun k _ _ _ _ => cls_of hZ k (hI k) (H k)

end PositivityTheory.Groth
