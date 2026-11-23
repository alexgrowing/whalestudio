import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchimedeanTruncatedRowUnipotentInvariantNonzero
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OnMatInfOfIsUnit
open NumberField GlobalTheory.CuspRep GlobalTheory.JSW GlobalTheory.JSW.MirCinf MeasureTheory
open scoped FourierTransform ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.archimedeanTruncatedRow_unipotent_invariant_nonzero : ∀ (E : Type) [Field E] [NumberField E] (n : ℕ) (ρ : Fin n), ∀ g ∈ levSetInf E n (ρ + 1), (∀ u ∈ GlobalTheory.SmGL.unipB (Cinf E) (Fin n), rowCutInf ρ ((u * g : GL (Fin n) (Cinf E)) : Matrix (Fin n) (Fin n) (Cinf E)) = rowCutInf ρ (g : Matrix (Fin n) (Fin n) (Cinf E))) ∧ ∀ w, ∃ j, j ≤ ρ ∧ rowCutInf ρ (g : Matrix (Fin n) (Fin n) (Cinf E)) j w ≠ 0 := by
  first | exact @GlobalTheory.JSW.MirCinf.rowCutInf_unipB_mul_levSetInf | exact GlobalTheory.JSW.MirCinf.rowCutInf_unipB_mul_levSetInf | (intros; apply GlobalTheory.JSW.MirCinf.rowCutInf_unipB_mul_levSetInf; all_goals assumption)
