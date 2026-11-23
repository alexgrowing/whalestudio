import Mathlib
import CompanionTheory.AutomorphicTheory.ProductFormulaTheory.GrothendieckRingPolynomial.GrothOfCls
import CompanionTheory.AutomorphicTheory.ProductFormulaTheory.GrothendieckRingPolynomial.PeelGood

namespace CompanionTheory.Groth

theorem groth_of_three (hZ : GlobalTheory.Published.SegmentRepresentation)
    (hI : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], Zc.Cos.LUnlinkedIrr k)
    (H : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k],
      CompanionTheory.Exh.MidP k ∧ CompanionTheory.Exh.RefineP k ∧ CompanionTheory.Exh.SwapP k) : GlobalTheory.Published.GrothendieckRingPolynomial :=
  groth_of_cls fun k _ _ _ _ => cls_of hZ k (hI k) (H k)

end CompanionTheory.Groth
