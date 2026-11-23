import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRingHomPadicAlgClNeZero
import Mathlib
open IsLocalRing
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_ringHom_padicAlgCl_ne_zero' : ∀ (B : Type) [CommRing B] [IsDomain B] [IsLocalRing B] [IsNoetherianRing B] [CharZero B], Finite (ResidueField B) → ∀ h : B, h ≠ 0 → ∃ (p : ℕ) (_ : Fact p.Prime) (χ : B →+* PadicAlgCl p), (∀ b, ‖χ b‖ ≤ 1) ∧ (∀ b ∈ maximalIdeal B, ‖χ b‖ < 1) ∧ χ h ≠ 0 := by
  first | exact @GlobalTheory.CurvePoint.exists_ringHom_padicAlgCl_ne_zero | exact GlobalTheory.CurvePoint.exists_ringHom_padicAlgCl_ne_zero | (intros; apply GlobalTheory.CurvePoint.exists_ringHom_padicAlgCl_ne_zero <;> assumption)
