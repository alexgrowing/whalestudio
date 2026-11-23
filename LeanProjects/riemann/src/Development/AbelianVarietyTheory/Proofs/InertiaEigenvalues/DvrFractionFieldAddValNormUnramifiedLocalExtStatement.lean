import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DvrFractionFieldAddValNormUnramifiedLocalExt
import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.OverExtAlgebraMap
open GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Unr Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dvrFractionFieldAddVal_norm_unramifiedLocalExt : ∀ (K K' : UQ) (d : ℕ) (φ : K.E →+* K'.E), IsUnrExt K K' d φ → ∀ y : K'.E, val K.O (@Algebra.norm K.E K'.E _ _ φ.toAlgebra y) = (d : ℤ) * val K'.O y := by
  first | exact @GlobalTheory.UnitLemma.Unr.NormValU.val_norm | exact GlobalTheory.UnitLemma.Unr.NormValU.val_norm | (intros; apply GlobalTheory.UnitLemma.Unr.NormValU.val_norm <;> assumption)
