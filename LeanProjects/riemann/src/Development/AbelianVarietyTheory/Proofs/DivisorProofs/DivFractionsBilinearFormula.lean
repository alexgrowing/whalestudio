import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HPolyAddTwo

set_option autoImplicit false

open MeasureTheory MvPolynomial GlobalTheory.FibLine

namespace GlobalTheory.FibLine.UnitaryInv

theorem det_smul_one (z : ℂ) : (z • (1 : ℂ →L[ℝ] ℂ)).det = Complex.normSq z := by
  rw [← Algebra.norm_complex_apply, Algebra.norm_apply, ContinuousLinearMap.det]
  congr 1

theorem ae_affine_ne (a b : ℂ) (h : a ≠ 0 ∨ b ≠ 0) : ∀ᵐ x : ℂ, a + b * x ≠ 0 := by
  rw [ae_iff]
  apply Set.Subsingleton.measure_zero
  intro x hx y hy
  simp only [ne_eq, not_not, Set.mem_setOf_eq] at hx hy
  by_cases hb : b = 0
  · rcases h with h | h
    · simp [hb, h] at hx
    · exact absurd hb h
  · apply mul_left_cancel₀ hb
    linear_combination hx - hy

theorem integral_moebius (a b c d : ℂ) (hD : a * d - b * c ≠ 0) (G : ℂ → ℂ) :
    ∫ y : ℂ, G y = ∫ x : ℂ, (Complex.normSq ((a * d - b * c) / (a + b * x) ^ 2)) •
      G ((c + d * x) / (a + b * x)) := by
  set s : Set ℂ := {x | a + b * x ≠ 0} with hs
  have hso : IsOpen s := isOpen_ne_fun (by fun_prop) continuous_const
  have hder : ∀ x ∈ s, HasFDerivWithinAt (fun x : ℂ => (c + d * x) / (a + b * x))
      (((a * d - b * c) / (a + b * x) ^ 2) • (1 : ℂ →L[ℝ] ℂ)) s x := by
    intro x hx
    have h1 : HasDerivAt (fun x : ℂ => c + d * x) d x := by
      simpa using ((hasDerivAt_id x).const_mul d).const_add c
    have h2 : HasDerivAt (fun x : ℂ => a + b * x) b x := by
      simpa using ((hasDerivAt_id x).const_mul b).const_add a
    have h3 := h1.div h2 hx
    have h4 : HasDerivAt (fun x : ℂ => (c + d * x) / (a + b * x)) ((a * d - b * c) / (a + b * x) ^ 2) x := by
      have e : (a * d - b * c) / (a + b * x) ^ 2
          = (d * (a + b * x) - (c + d * x) * b) / (a + b * x) ^ 2 := by ring
      rw [e]
      exact h3
    exact h4.complexToReal_fderiv.hasFDerivWithinAt
  have hinj : Set.InjOn (fun x : ℂ => (c + d * x) / (a + b * x)) s := by
    intro x hx y hy hxy
    have hx' : a + b * x ≠ 0 := hx
    have hy' : a + b * y ≠ 0 := hy
    simp only at hxy
    rw [div_eq_div_iff hx' hy'] at hxy
    apply mul_left_cancel₀ hD
    linear_combination hxy
  have key := integral_image_eq_integral_abs_det_fderiv_smul (volume : Measure ℂ) hso.measurableSet hder hinj G
  have hab : a ≠ 0 ∨ b ≠ 0 := by
    by_contra h
    push_neg at h
    simp [h.1, h.2] at hD
  have hdb : d ≠ 0 ∨ -b ≠ 0 := by
    by_contra h
    push_neg at h
    have hb : b = 0 := by simpa using h.2
    simp [h.1, hb] at hD
  have him : ∀ᵐ y : ℂ, y ∈ (fun x : ℂ => (c + d * x) / (a + b * x)) '' s := by
    filter_upwards [ae_affine_ne d (-b) hdb] with y hy
    have e1 : a + b * ((a * y - c) / (d + -b * y)) = (a * d - b * c) / (d + -b * y) := by
      rw [eq_div_iff hy, add_mul, mul_assoc, div_mul_cancel₀ _ hy]
      ring
    have e2 : c + d * ((a * y - c) / (d + -b * y)) = y * ((a * d - b * c) / (d + -b * y)) := by
      rw [← mul_div_assoc y, eq_div_iff hy, add_mul, mul_assoc, div_mul_cancel₀ _ hy]
      ring
    have e3 : (a * d - b * c) / (d + -b * y) ≠ 0 := div_ne_zero hD hy
    refine ⟨(a * y - c) / (d + -b * y), ?_, ?_⟩
    · show a + b * ((a * y - c) / (d + -b * y)) ≠ 0
      rw [e1]; exact e3
    · show (c + d * ((a * y - c) / (d + -b * y))) / (a + b * ((a * y - c) / (d + -b * y))) = y
      rw [e1, e2, mul_div_assoc, div_self e3, mul_one]
  have hs' : ∀ᵐ x : ℂ, x ∈ s := ae_affine_ne a b hab
  rw [Measure.restrict_eq_self_of_ae_mem him, Measure.restrict_eq_self_of_ae_mem hs'] at key
  rw [key]
  congr 1
  ext x
  rw [det_smul_one, abs_of_nonneg (Complex.normSq_nonneg _)]

theorem qMat_eq (H : Matrix (Fin 2) (Fin 2) ℂ) (x : ℂ) :
    qMat H x = (H 0 0 + H 0 1 * x + H 1 0 * starRingEnd ℂ x + H 1 1 * (x * starRingEnd ℂ x)) /
      (1 + x * starRingEnd ℂ x) := by
  have : ((1 + ‖x‖ ^ 2 : ℝ) : ℂ) = 1 + x * starRingEnd ℂ x := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]; push_cast; ring
  simp only [qMat, qCoef, entries, lineVec, Fintype.sum_prod_type, Fin.sum_univ_two, this, smul_eq_mul,
    Matrix.cons_val_zero, Matrix.cons_val_one, map_one]
  ring

theorem fsDens_eq (x : ℂ) :
    (fsDens x : ℂ) = 1 / (Real.pi * (1 + x * starRingEnd ℂ x) ^ 2) := by
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, fsDens]; push_cast; ring

theorem one_add_ne (x : ℂ) : 1 + x * starRingEnd ℂ x ≠ 0 := by
  rw [Complex.mul_conj]
  have := Complex.normSq_nonneg x
  exact_mod_cast (by linarith : (1 + Complex.normSq x) ≠ 0)

theorem div_fractions_bilinear_formula (h0 h1 h2 h3 A B C D N : ℂ) (hA : A ≠ 0) (hB : B ≠ 0) (hN : N ≠ 0) :
    (h0 + h1 * (C / A) + h2 * (D / B) + h3 * (C / A * (D / B))) / (N / (A * B))
      = (h0 * (A * B) + h1 * (C * B) + h2 * (D * A) + h3 * (C * D)) / N := by
  field_simp

theorem integral_qMat_unitary_conj (U : Matrix (Fin 2) (Fin 2) ℂ) (hU : U ∈ Matrix.unitaryGroup (Fin 2) ℂ)
    (H : Matrix (Fin 2) (Fin 2) ℂ) (k : ℕ) :
    ∫ x : ℂ, qMat (U * H * star U) x ^ k * (fsDens x : ℂ) = ∫ x : ℂ, qMat H x ^ k * (fsDens x : ℂ) := by
  have h1 : U * star U = 1 := Matrix.mem_unitaryGroup_iff.1 hU
  have e := fun i j => congrFun (congrFun h1 i) j
  have e00 := e 0 0
  have e01 := e 0 1
  have e10 := e 1 0
  have e11 := e 1 1
  simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.star_apply, Matrix.one_apply, RCLike.star_def,
    if_true, Fin.zero_eq_one_iff, Fin.one_eq_zero_iff, OfNat.ofNat_ne_one, if_false] at e00 e01 e10 e11
  set p := U 0 0 with hp
  set q := U 0 1 with hq
  set r := U 1 0 with hr
  set t := U 1 1 with ht
  set a := starRingEnd ℂ p with ha
  set c := starRingEnd ℂ q with hc
  set b := starRingEnd ℂ r with hb
  set d := starRingEnd ℂ t with hd
  have hDD : (a * d - b * c) * (p * t - r * q) = 1 := by
    linear_combination (r * b + t * d) * e00 + e11 - (r * a + t * c) * e01 - 0 * e10
  have hD : a * d - b * c ≠ 0 := left_ne_zero_of_mul_eq_one hDD
  rw [integral_moebius a b c d hD (fun x => qMat H x ^ k * (fsDens x : ℂ))]
  have hab : a ≠ 0 ∨ b ≠ 0 := by
    by_contra h
    push_neg at h
    simp [h.1, h.2] at hD
  apply integral_congr_ae
  filter_upwards [ae_affine_ne a b hab] with x hx
  set y := starRingEnd ℂ x with hy
  have hcj : starRingEnd ℂ (a + b * x) = p + r * y := by simp [ha, hb, hy]
  have hcj2 : starRingEnd ℂ (c + d * x) = q + t * y := by simp [hc, hd, hy]
  have hcj3 : starRingEnd ℂ (a * d - b * c) = p * t - r * q := by simp [ha, hb, hc, hd]
  have hx' : p + r * y ≠ 0 := by rw [← hcj]; simpa only [ne_eq, map_eq_zero] using hx
  have hN : 1 + x * y ≠ 0 := one_add_ne x
  have hsum : (a + b * x) * (p + r * y) + (c + d * x) * (q + t * y) = 1 + x * y := by
    linear_combination e00 + x * e01 + y * e10 + x * y * e11
  have hm : 1 + (c + d * x) / (a + b * x) * ((q + t * y) / (p + r * y))
      = (1 + x * y) / ((a + b * x) * (p + r * y)) := by
    rw [← hsum, add_div ((a + b * x) * (p + r * y)), div_self (mul_ne_zero hx hx'), div_mul_div_comm]
  have hq' : qMat H ((c + d * x) / (a + b * x)) = qMat (U * H * star U) x := by
    rw [qMat_eq, qMat_eq, map_div₀, hcj, hcj2, hm]
    simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.star_apply, RCLike.star_def]
    rw [← hy, ← hp, ← hq, ← hr, ← ht, ← ha, ← hb, ← hc, ← hd]
    rw [div_fractions_bilinear_formula _ _ _ _ _ _ _ _ _ hx hx' hN]
    ring
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hf : ((Complex.normSq ((a * d - b * c) / (a + b * x) ^ 2) : ℝ) : ℂ) *
      (fsDens ((c + d * x) / (a + b * x)) : ℂ) = fsDens x := by
    rw [fsDens_eq, fsDens_eq, ← Complex.mul_conj, map_div₀, map_div₀, map_pow, hcj, hcj2, hcj3, hm, ← hy,
      div_mul_div_comm, hDD]
    generalize a + b * x = A at *
    generalize p + r * y = B at *
    generalize 1 + x * y = N at *
    field_simp
  simp only [Complex.real_smul]
  rw [hq', ← hf]
  ring

end GlobalTheory.FibLine.UnitaryInv
