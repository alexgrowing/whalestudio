import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralSymplecticPreimageEq
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExtMapApply
open Matrix MeasureTheory Set GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe GlobalTheory.TorsionForm
open scoped ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_symplectic_preimage_eq : ∀ {g : ℕ} {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] (γ : Sp g) (D : Set (Fl g)) (φ : Fl g → F), ∫ x in (fun x : Fl g => x ᵥ* (γ⁻¹).mat) ⁻¹' D, φ (x ᵥ* (γ⁻¹).mat) = ∫ x in D, φ x := by
  first | exact @GlobalTheory.SympChange.setIntegral_vecMul_inv | exact GlobalTheory.SympChange.setIntegral_vecMul_inv | (intros; apply GlobalTheory.SympChange.setIntegral_vecMul_inv <;> assumption)
