import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MonicCoeffNatDegreeSubEqMulCmConj
import Mathlib
open NumberField Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.monic_coeff_natDegree_sub_eq_mul_cmConj : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (P : Polynomial E),
    P.Monic → P.natDegree = n → (∀ (τ : E →+* ℂ), ∀ z ∈ (P.map τ).roots, ‖z‖ = 1) →
    ∀ i ≤ n, P.coeff (n - i) = P.coeff 0 * IsCMField.complexConj E (P.coeff i) := by
  first | exact @GlobalTheory.monic_coeff_natDegree_sub_eq_mul_complexConj | exact GlobalTheory.monic_coeff_natDegree_sub_eq_mul_complexConj | (intros; apply GlobalTheory.monic_coeff_natDegree_sub_eq_mul_complexConj <;> assumption)
