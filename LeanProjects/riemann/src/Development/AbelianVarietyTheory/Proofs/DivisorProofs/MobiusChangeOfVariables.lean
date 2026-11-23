import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DivFractionsBilinearFormula

set_option autoImplicit false

open MeasureTheory
open scoped ENNReal

namespace GlobalTheory.FibLine.MoebiusLintegral

open GlobalTheory.FibLine.UnitaryInv

theorem lintegral_moebius (β c : ℂ) (hc : c ≠ 0) (H : ℂ → ℝ≥0∞) (_hH : Measurable H) :
    ∫⁻ x : ℂ, ENNReal.ofReal (‖c / (1 + β * x) ^ 2‖ ^ 2) * H (c * x / (1 + β * x)) = ∫⁻ y : ℂ, H y := by
  set s : Set ℂ := {x | 1 + β * x ≠ 0} with hs
  have hso : IsOpen s := isOpen_ne_fun (by fun_prop) continuous_const
  have hder : ∀ x ∈ s, HasFDerivWithinAt (fun x : ℂ => c * x / (1 + β * x))
      ((c / (1 + β * x) ^ 2) • (1 : ℂ →L[ℝ] ℂ)) s x := by
    intro x hx
    have h1 : HasDerivAt (fun x : ℂ => c * x) c x := by
      simpa using (hasDerivAt_id x).const_mul c
    have h2 : HasDerivAt (fun x : ℂ => 1 + β * x) β x := by
      simpa using ((hasDerivAt_id x).const_mul β).const_add 1
    have h3 := h1.div h2 hx
    have h4 : HasDerivAt (fun x : ℂ => c * x / (1 + β * x)) (c / (1 + β * x) ^ 2) x := by
      have e : c / (1 + β * x) ^ 2 = (c * (1 + β * x) - (c * x) * β) / (1 + β * x) ^ 2 := by ring
      rw [e]
      exact h3
    exact h4.complexToReal_fderiv.hasFDerivWithinAt
  have hinj : Set.InjOn (fun x : ℂ => c * x / (1 + β * x)) s := by
    intro x hx y hy hxy
    have hx' : 1 + β * x ≠ 0 := hx
    have hy' : 1 + β * y ≠ 0 := hy
    simp only at hxy
    rw [div_eq_div_iff hx' hy'] at hxy
    apply mul_left_cancel₀ hc
    linear_combination hxy
  have key := lintegral_image_eq_lintegral_abs_det_fderiv_mul (volume : Measure ℂ) hso.measurableSet hder hinj H
  have him : ∀ᵐ y : ℂ, y ∈ (fun x : ℂ => c * x / (1 + β * x)) '' s := by
    filter_upwards [ae_affine_ne c (-β) (Or.inl hc)] with y hy
    have e1 : 1 + β * (y / (c + -β * y)) = c / (c + -β * y) := by
      rw [eq_div_iff hy, add_mul, mul_assoc, div_mul_cancel₀ _ hy]
      ring
    have e2 : c * (y / (c + -β * y)) = y * (c / (c + -β * y)) := by ring
    have e3 : c / (c + -β * y) ≠ 0 := div_ne_zero hc hy
    refine ⟨y / (c + -β * y), ?_, ?_⟩
    · show 1 + β * (y / (c + -β * y)) ≠ 0
      rw [e1]; exact e3
    · show (c * (y / (c + -β * y))) / (1 + β * (y / (c + -β * y))) = y
      rw [e1, e2, mul_div_assoc, div_self e3, mul_one]
  have hs' : ∀ᵐ x : ℂ, x ∈ s := ae_affine_ne 1 β (Or.inl one_ne_zero)
  rw [Measure.restrict_eq_self_of_ae_mem him, Measure.restrict_eq_self_of_ae_mem hs'] at key
  rw [key]
  congr 1
  ext x
  rw [det_smul_one, abs_of_nonneg (Complex.normSq_nonneg _), Complex.normSq_eq_norm_sq]

end GlobalTheory.FibLine.MoebiusLintegral
