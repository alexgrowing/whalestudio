import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PeriodVectorMoebiusTransform
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExtMapApply
open Matrix MeasureTheory Set GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe GlobalTheory.TorsionForm
open scoped ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.period_vector_moebius_transform : ∀ {g : ℕ} (γ : Sp g) (T : Matrix (Fin g) (Fin g) ℂ) (x : Fl g), IsUnit (den γ T) → per T x ᵥ* (den γ T)⁻¹ = per (moeb γ T) (x ᵥ* (γ⁻¹).mat) := by
  first | exact @GlobalTheory.TorsionForm.per_vecMul_den_inv_eq_per_moeb | exact GlobalTheory.TorsionForm.per_vecMul_den_inv_eq_per_moeb | (intros; apply GlobalTheory.TorsionForm.per_vecMul_den_inv_eq_per_moeb <;> assumption)
