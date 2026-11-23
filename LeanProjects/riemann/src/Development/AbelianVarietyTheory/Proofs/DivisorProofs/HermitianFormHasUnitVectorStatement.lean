import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianFormHasUnitVector
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GoodRing
open Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermitian_form_has_unit_vector : ∀ {R : Type} [CommRing R] {n : Type} [Fintype n] [DecidableEq n] [Nonempty n] (τ : R →+* R) (H H' : Matrix n n R) (p w v : R), (∀ a, τ (τ a) = a) → w + τ w = 1 → (w - τ w) * v = 1 → Formalism.UG.cT τ H = H → H * H' = 1 → (∀ a, τ a = a → (¬ ∃ s, a = p * s) → IsUnit a) → (¬ ∃ s, p * s = 1) → ∃ e : n → R, IsUnit (Formalism.UG.hform τ H e e) := by
  first | exact @GlobalTheory.hform_exists_unit_value | exact GlobalTheory.hform_exists_unit_value | (intros; apply GlobalTheory.hform_exists_unit_value <;> assumption)
