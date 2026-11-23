import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeDetRelationOfLsmulShift
import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.QuotientEigenDifference
open scoped NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.latticeDetRelation_of_lsmul_shift : ∀ (C : Type) [Field C] (w : Valuation C ℝ≥0) (ℓ : C), 0 < w ℓ → w ℓ < 1 → ∀ (p q : ℕ) (F : Submodule C (Fin (p + q) → C)) (X0 : Submodule w.valuationSubring (Fin (p + q) → C)) (L : Submodule w.valuationSubring ((Fin (p + q) → C) ⧸ F)) (M : Submodule w.valuationSubring (Fin (p + q) → C)) (y : ℝ) (d : w.valuationSubring), d ≠ 0 → GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.DetRel w ℓ F (X0.map (LinearMap.lsmul w.valuationSubring (Fin (p + q) → C) d)) L M y → GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.DetRel w ℓ F X0 L M (y - ((p + q : ℕ) : ℝ) * GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.addVal w ℓ (d : C)) := by
  first | exact @GlobalTheory.detRel_of_detRel_lsmul | exact GlobalTheory.detRel_of_detRel_lsmul | (intros; apply GlobalTheory.detRel_of_detRel_lsmul <;> assumption)
