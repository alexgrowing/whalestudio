import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsFlatLift
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatModPSquaredTorsion
open GlobalTheory GlobalTheory.DI
theorem _root_.GlobalTheory.T.flat_mod_p_squared_torsion : ∀ (p : ℕ) [Fact p.Prime] {B : Type} [CommRing B] (φ : ZMod (p ^ 2) →+* B), φ.Flat → ∀ w : B, (p : B) * w = 0 ↔ ∃ v, w = p * v := by
  first | exact @_root_.GlobalTheory.flat_zmod_sq_mul_p_eq_zero_iff | exact _root_.GlobalTheory.flat_zmod_sq_mul_p_eq_zero_iff | (intros; apply _root_.GlobalTheory.flat_zmod_sq_mul_p_eq_zero_iff <;> assumption)
