import Mathlib

namespace ReciprocityTheory.ChartRestriction.G.I2

open MeasureTheory

def monomialOfMultiindex {g : ℕ} (α : Fin g →₀ ℕ) (z : EuclideanSpace ℂ (Fin g)) : ℂ :=
  ∏ i ∈ α.support, z i ^ α i

theorem fa1Mono_eq {g : ℕ} (α : Fin g →₀ ℕ) (z : EuclideanSpace ℂ (Fin g)) :
    monomialOfMultiindex α z = ∏ i, z i ^ α i := by
  unfold monomialOfMultiindex
  exact Finset.prod_subset (Finset.subset_univ _) fun i _ hi => by
    rw [Finsupp.notMem_support_iff.mp hi, pow_zero]

theorem fa1Mono_continuous {g : ℕ} (α : Fin g →₀ ℕ) : Continuous (monomialOfMultiindex α) := by
  have h : monomialOfMultiindex α = fun z : EuclideanSpace ℂ (Fin g) => ∏ i, z i ^ α i := funext (fa1Mono_eq α)
  rw [h]
  exact continuous_finsetProd _ fun i _ => (PiLp.continuous_apply 2 _ i).pow _

theorem fa1Mono_norm_le {g : ℕ} (α : Fin g →₀ ℕ) (z : EuclideanSpace ℂ (Fin g)) :
    ‖monomialOfMultiindex α z‖ ≤ ‖z‖ ^ (∑ i, α i) := by
  rw [fa1Mono_eq, norm_prod, ← Finset.prod_pow_eq_pow_sum]
  refine Finset.prod_le_prod (fun i _ => norm_nonneg _) fun i _ => ?_
  rw [norm_pow]
  exact pow_le_pow_left₀ (norm_nonneg _) (PiLp.norm_apply_le z i) _

theorem fa1Mono_smul {g : ℕ} (α : Fin g →₀ ℕ) (r : ℝ) (z : EuclideanSpace ℂ (Fin g)) :
    monomialOfMultiindex α (r • z) = (r : ℂ) ^ (∑ i, α i) * monomialOfMultiindex α z := by
  rw [fa1Mono_eq, fa1Mono_eq, ← Finset.prod_pow_eq_pow_sum, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [PiLp.smul_apply, Complex.real_smul, mul_pow]

theorem pow_mul_exp_neg_mul_sq_le (n : ℕ) {b t : ℝ} (hb : 0 < b) (ht : 0 ≤ t) :
    t ^ n * Real.exp (-b * t ^ 2) ≤
      (1 + n.factorial * (2 / b) ^ n) * Real.exp (-(b / 2) * t ^ 2) := by
  have hx : 0 ≤ b / 2 * t ^ 2 := by positivity
  have h1 : 1 ≤ Real.exp (b / 2 * t ^ 2) := Real.one_le_exp hx
  have h2 : (b / 2 * t ^ 2) ^ n / n.factorial ≤ Real.exp (b / 2 * t ^ 2) :=
    Real.pow_div_factorial_le_exp (x := b / 2 * t ^ 2) hx n
  have h3 : t ^ n ≤ 1 + t ^ (2 * n) := by
    rcases le_total t 1 with h | h
    · have : t ^ n ≤ 1 := pow_le_one₀ ht h
      linarith [pow_nonneg ht (2 * n)]
    · have : t ^ n ≤ t ^ (2 * n) := pow_le_pow_right₀ h (by omega)
      linarith
  have h4 : t ^ (2 * n) = (2 / b) ^ n * (b / 2 * t ^ 2) ^ n := by
    rw [pow_mul, ← mul_pow]
    congr 1
    field_simp
  have hfac : (0 : ℝ) < n.factorial := by exact_mod_cast Nat.factorial_pos n
  have h5 : t ^ (2 * n) ≤ n.factorial * (2 / b) ^ n * Real.exp (b / 2 * t ^ 2) := by
    rw [h4]
    have h2' := (div_le_iff₀ hfac).mp h2
    have hb2 : 0 ≤ (2 / b) ^ n := by positivity
    nlinarith
  have hexp : Real.exp (b / 2 * t ^ 2) * Real.exp (-b * t ^ 2) = Real.exp (-(b / 2) * t ^ 2) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have h6 : t ^ n ≤ (1 + n.factorial * (2 / b) ^ n) * Real.exp (b / 2 * t ^ 2) := by
    nlinarith
  calc t ^ n * Real.exp (-b * t ^ 2)
      ≤ (1 + n.factorial * (2 / b) ^ n) * Real.exp (b / 2 * t ^ 2) * Real.exp (-b * t ^ 2) :=
        mul_le_mul_of_nonneg_right h6 (Real.exp_pos _).le
    _ = (1 + n.factorial * (2 / b) ^ n) * Real.exp (-(b / 2) * t ^ 2) := by
        rw [mul_assoc, hexp]

theorem integrable_exp_neg_mul_norm_sq_euclidean {g : ℕ} {b : ℝ} (hb : 0 < b) :
    Integrable (fun z : EuclideanSpace ℂ (Fin g) => Real.exp (-b * ‖z‖ ^ 2)) := by
  have hc := GaussianFourier.integrable_cexp_neg_mul_sq_norm_add (V := EuclideanSpace ℂ (Fin g))
    (b := (b : ℂ)) (by simpa using hb) 0 0
  refine hc.norm.congr (Filter.Eventually.of_forall fun z => ?_)
  simp only [zero_mul, add_zero]
  rw [Complex.norm_exp]
  congr 1
  simp [← Complex.ofReal_pow]

theorem integrable_norm_pow_mul_exp_neg_mul_norm_sq_euclidean {g : ℕ} (n : ℕ) {b : ℝ} (hb : 0 < b) :
    Integrable (fun z : EuclideanSpace ℂ (Fin g) => ‖z‖ ^ n * Real.exp (-b * ‖z‖ ^ 2)) := by
  have hb2 : 0 < b / 2 := by positivity
  refine ((integrable_exp_neg_mul_norm_sq_euclidean (g := g) hb2).const_mul (1 + n.factorial * (2 / b) ^ n)).mono' ?_ ?_
  · exact (by fun_prop : Continuous fun z : EuclideanSpace ℂ (Fin g) =>
      ‖z‖ ^ n * Real.exp (-b * ‖z‖ ^ 2)).aestronglyMeasurable
  · refine Filter.Eventually.of_forall fun z => ?_
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact pow_mul_exp_neg_mul_sq_le n hb (norm_nonneg z)

theorem integrable_of_norm_le_gaussian {g : ℕ} {E : Type*} [NormedAddCommGroup E]
    {f : EuclideanSpace ℂ (Fin g) → E} (hf : Continuous f) (n : ℕ) {b C : ℝ} (hb : 0 < b)
    (h : ∀ z, ‖f z‖ ≤ C * (‖z‖ ^ n * Real.exp (-b * ‖z‖ ^ 2))) : Integrable f := by
  exact ((integrable_norm_pow_mul_exp_neg_mul_norm_sq_euclidean n hb).const_mul C).mono' hf.aestronglyMeasurable
    (Filter.Eventually.of_forall h)

theorem integrable_monomial_mul_conj_gaussian {g : ℕ} (α β : Fin g →₀ ℕ) :
    Integrable (fun z : EuclideanSpace ℂ (Fin g) =>
      monomialOfMultiindex α z * (starRingEnd ℂ) (monomialOfMultiindex β z) * (Real.exp (-‖z‖ ^ 2) : ℂ)) := by
  have hcont : Continuous fun z : EuclideanSpace ℂ (Fin g) =>
      monomialOfMultiindex α z * (starRingEnd ℂ) (monomialOfMultiindex β z) * (Real.exp (-‖z‖ ^ 2) : ℂ) :=
    ((fa1Mono_continuous α).mul (Complex.continuous_conj.comp (fa1Mono_continuous β))).mul
      (Complex.continuous_ofReal.comp (Real.continuous_exp.comp (continuous_norm.pow 2).neg))
  refine integrable_of_norm_le_gaussian hcont (∑ i, α i + ∑ i, β i) one_pos (C := 1) fun z => ?_
  rw [norm_mul, norm_mul, Complex.norm_conj, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _), one_mul, neg_one_mul, pow_add]
  have h1 := fa1Mono_norm_le α z
  have h2 := fa1Mono_norm_le β z
  have he := (Real.exp_pos (-‖z‖ ^ 2)).le
  gcongr

theorem integrable_norm_monomial_sq_gaussian {g : ℕ} (α : Fin g →₀ ℕ) {b : ℝ} (hb : 0 < b) :
    Integrable (fun z : EuclideanSpace ℂ (Fin g) => ‖monomialOfMultiindex α z‖ ^ 2 * Real.exp (-b * ‖z‖ ^ 2)) := by
  have hcont : Continuous fun z : EuclideanSpace ℂ (Fin g) =>
      ‖monomialOfMultiindex α z‖ ^ 2 * Real.exp (-b * ‖z‖ ^ 2) :=
    ((fa1Mono_continuous α).norm.pow 2).mul
      (Real.continuous_exp.comp (continuous_const.mul (continuous_norm.pow 2)))
  refine integrable_of_norm_le_gaussian hcont (2 * ∑ i, α i) hb (C := 1) fun z => ?_
  rw [one_mul, Real.norm_eq_abs, abs_of_nonneg (by positivity), pow_mul']
  have h1 := fa1Mono_norm_le α z
  gcongr

noncomputable def coordinateRotation {g : ℕ} (j : Fin g) (u : Circle) :
    EuclideanSpace ℂ (Fin g) ≃ₗᵢ[ℝ] EuclideanSpace ℂ (Fin g) :=
  LinearIsometryEquiv.piLpCongrRight 2
    (fun i => if i = j then rotation u else LinearIsometryEquiv.refl ℝ ℂ)

theorem fa1Rot_apply {g : ℕ} (j : Fin g) (u : Circle) (z : EuclideanSpace ℂ (Fin g)) (i : Fin g) :
    coordinateRotation j u z i = (if i = j then (u : ℂ) else 1) * z i := by
  simp only [coordinateRotation, LinearIsometryEquiv.piLpCongrRight_apply]
  split_ifs with h
  · simp [rotation_apply]
  · simp

theorem fa1Mono_rot {g : ℕ} (α : Fin g →₀ ℕ) (j : Fin g) (u : Circle)
    (z : EuclideanSpace ℂ (Fin g)) :
    monomialOfMultiindex α (coordinateRotation j u z) = (u : ℂ) ^ (α j) * monomialOfMultiindex α z := by
  rw [fa1Mono_eq, fa1Mono_eq]
  simp only [fa1Rot_apply, mul_pow, Finset.prod_mul_distrib, ite_pow, one_pow,
    Finset.prod_ite_eq', Finset.mem_univ, if_true]

theorem integral_monomial_mul_conj_gaussian_eq_zero {g : ℕ} {α β : Fin g →₀ ℕ} (h : α ≠ β) :
    ∫ z : EuclideanSpace ℂ (Fin g),
      monomialOfMultiindex α z * (starRingEnd ℂ) (monomialOfMultiindex β z) * (Real.exp (-‖z‖ ^ 2) : ℂ) = 0 := by
  obtain ⟨j, hj⟩ : ∃ j, α j ≠ β j := by
    by_contra hcon
    exact h (Finsupp.ext fun j => not_not.mp fun hne => hcon ⟨j, hne⟩)
  have hm : ((α j : ℝ) - β j) ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast hj)
  set u : Circle := Circle.exp (Real.pi / ((α j : ℝ) - β j)) with hu
  set F : EuclideanSpace ℂ (Fin g) → ℂ := fun z =>
    monomialOfMultiindex α z * (starRingEnd ℂ) (monomialOfMultiindex β z) * (Real.exp (-‖z‖ ^ 2) : ℂ) with hF
  have hc : (u : ℂ) ^ (α j) * (starRingEnd ℂ) ((u : ℂ) ^ (β j)) = -1 := by
    rw [hu, Circle.coe_exp, map_pow, ← Complex.exp_conj, ← Complex.exp_nat_mul,
      ← Complex.exp_nat_mul, ← Complex.exp_add]
    have hm' : ((α j : ℂ) - β j) ≠ 0 := by exact_mod_cast hm
    have : (α j : ℂ) * (↑(Real.pi / ((α j : ℝ) - β j)) * Complex.I) +
        (β j : ℂ) * (starRingEnd ℂ) (↑(Real.pi / ((α j : ℝ) - β j)) * Complex.I) =
        Real.pi * Complex.I := by
      rw [map_mul, Complex.conj_ofReal, Complex.conj_I]
      push_cast
      field_simp
      ring
    rw [this, Complex.exp_pi_mul_I]
  have hrot : ∀ z, F (coordinateRotation j u z) =
      ((u : ℂ) ^ (α j) * (starRingEnd ℂ) ((u : ℂ) ^ (β j))) * F z := by
    intro z
    simp only [hF, fa1Mono_rot, LinearIsometryEquiv.norm_map, map_mul]
    ring
  have hint : ∫ z, F (coordinateRotation j u z) = ∫ z, F z :=
    (coordinateRotation j u).measurePreserving.integral_comp (coordinateRotation j u).toHomeomorph.measurableEmbedding F
  simp_rw [hrot, hc] at hint
  rw [integral_const_mul] at hint
  linear_combination (-1 / 2 : ℂ) * hint

theorem integral_norm_monomial_sq_gaussian_pos {g : ℕ} (α : Fin g →₀ ℕ) :
    0 < ∫ z : EuclideanSpace ℂ (Fin g), ‖monomialOfMultiindex α z‖ ^ 2 * Real.exp (-‖z‖ ^ 2) := by
  set f : EuclideanSpace ℂ (Fin g) → ℝ := fun z => ‖monomialOfMultiindex α z‖ ^ 2 * Real.exp (-‖z‖ ^ 2) with hf
  have hcont : Continuous f :=
    ((fa1Mono_continuous α).norm.pow 2).mul (Real.continuous_exp.comp (continuous_norm.pow 2).neg)
  have hint : Integrable f := by
    have := integrable_norm_monomial_sq_gaussian α one_pos
    simpa [neg_one_mul] using this
  have hnn : 0 ≤ f := fun z => by
    simp only [Pi.zero_apply, hf]
    positivity
  rw [integral_pos_iff_support_of_nonneg hnn hint]
  let z₀ : EuclideanSpace ℂ (Fin g) := WithLp.toLp 2 (fun _ => (1 : ℂ))
  have hz₁ : monomialOfMultiindex α z₀ = 1 := by
    rw [fa1Mono_eq]
    simp [z₀]
  have hz₀ : f z₀ ≠ 0 := by
    simp only [hf, hz₁, norm_one, one_pow, one_mul]
    exact (Real.exp_pos _).ne'
  exact hcont.isOpen_support.measure_pos _ ⟨z₀, hz₀⟩

theorem integral_norm_monomial_sq_gaussian_half {g : ℕ} (α : Fin g →₀ ℕ) :
    ∫ z : EuclideanSpace ℂ (Fin g), ‖monomialOfMultiindex α z‖ ^ 2 * Real.exp (-(1 / 2) * ‖z‖ ^ 2) =
      2 ^ (g + ∑ i, α i) *
        ∫ z : EuclideanSpace ℂ (Fin g), ‖monomialOfMultiindex α z‖ ^ 2 * Real.exp (-‖z‖ ^ 2) := by
  have hs2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hpt : ∀ x : EuclideanSpace ℂ (Fin g),
      ‖monomialOfMultiindex α (Real.sqrt 2 • x)‖ ^ 2 * Real.exp (-(1 / 2) * ‖Real.sqrt 2 • x‖ ^ 2) =
        2 ^ (∑ i, α i) * (‖monomialOfMultiindex α x‖ ^ 2 * Real.exp (-‖x‖ ^ 2)) := by
    intro x
    rw [fa1Mono_smul, norm_mul, norm_pow, Complex.norm_real, norm_smul,
      Real.norm_of_nonneg (Real.sqrt_nonneg 2), mul_pow, mul_pow, ← pow_mul,
      mul_comm (∑ i, α i) 2, pow_mul, hs2, show -(1 / 2) * (2 * ‖x‖ ^ 2) = -‖x‖ ^ 2 by ring]
    ring
  have e1 : ∫ x : EuclideanSpace ℂ (Fin g),
      ‖monomialOfMultiindex α (Real.sqrt 2 • x)‖ ^ 2 * Real.exp (-(1 / 2) * ‖Real.sqrt 2 • x‖ ^ 2) =
        2 ^ (∑ i, α i) * ∫ x : EuclideanSpace ℂ (Fin g), ‖monomialOfMultiindex α x‖ ^ 2 * Real.exp (-‖x‖ ^ 2) := by
    rw [← integral_const_mul]
    exact integral_congr_ae (Filter.Eventually.of_forall hpt)
  have hdim : |(Real.sqrt 2 ^ Module.finrank ℝ (EuclideanSpace ℂ (Fin g)))⁻¹| = ((2 : ℝ) ^ g)⁻¹ := by
    rw [finrank_real_of_complex, finrank_euclideanSpace_fin, pow_mul, hs2,
      abs_of_pos (by positivity)]
  have e2 := MeasureTheory.Measure.integral_comp_smul (volume : Measure (EuclideanSpace ℂ (Fin g)))
    (fun z => ‖monomialOfMultiindex α z‖ ^ 2 * Real.exp (-(1 / 2) * ‖z‖ ^ 2)) (Real.sqrt 2)
  beta_reduce at e2
  rw [hdim, smul_eq_mul, e1] at e2
  have h2g : (2 : ℝ) ^ g ≠ 0 := by positivity
  rw [pow_add, mul_assoc, e2, ← mul_assoc, mul_inv_cancel₀ h2g, one_mul]

end ReciprocityTheory.ChartRestriction.G.I2
