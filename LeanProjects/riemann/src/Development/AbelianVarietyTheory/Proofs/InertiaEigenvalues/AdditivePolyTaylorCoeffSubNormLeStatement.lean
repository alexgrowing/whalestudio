import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdditivePolyTaylorCoeffSubNormLe
import Mathlib
open Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.norm_taylor_coeff_sub_coeff_le_norm_l : ∀ (l : ℕ) [Fact l.Prime] (E : ℕ) (a : ℕ → ℂ_[l]) (W : ℂ_[l]), (∀ k, k ≤ E → ‖a k‖ ≤ 1) → ‖W‖ ≤ 1 → ∀ j : ℕ, 1 ≤ j → ‖(Polynomial.taylor W (∑ k ∈ Finset.range (E + 1), Polynomial.monomial (l ^ k) (a k) : Polynomial ℂ_[l])).coeff j - (∑ k ∈ Finset.range (E + 1), Polynomial.monomial (l ^ k) (a k) : Polynomial ℂ_[l]).coeff j‖ ≤ ‖(l : ℂ_[l])‖ := by
  first | exact @GlobalTheory.additive_poly_taylor_coeff_sub_norm_le | exact GlobalTheory.additive_poly_taylor_coeff_sub_norm_le | (intros; apply GlobalTheory.additive_poly_taylor_coeff_sub_norm_le <;> assumption)
