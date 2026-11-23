import Mathlib
import Formalism.GL3MeanSquares.InverseNormLeOfIntegerInner

namespace Formalism.HermitianLattices.LatticeEstimates

open Finset MeasureTheory Matrix Real
open Formalism.HermitianLattices.TraceIntegrality
open Formalism.LogVandermondeBounds.flipTwoThree (Interlace B0 len)
open scoped ComplexOrder

theorem moduli_minimum_bound : Ms_min := by
  intro K _ _ x hx
  have hx' : (x : K) ≠ 0 := by simpa using hx
  have hN : (1:ℝ) ≤ ∏ φ : K →+* ℂ, ‖φ (x:K)‖ := by
    have h1 : (algebraMap ℚ ℂ) (Algebra.norm ℚ (x:K)) = ∏ σ : K →ₐ[ℚ] ℂ, σ (x:K) :=
      Algebra.norm_eq_prod_embeddings ℚ ℂ (x:K)
    have h2 : ∏ φ : K →+* ℂ, ‖φ (x:K)‖ = ‖(algebraMap ℚ ℂ) (Algebra.norm ℚ (x:K))‖ := by
      rw [h1, norm_prod]
      exact Fintype.prod_equiv (RingHom.equivRatAlgHom K ℂ) _ _ (fun φ => rfl)
    rw [h2, ← Algebra.coe_norm_int x]
    have h3 : Algebra.norm ℤ x ≠ 0 := Algebra.norm_ne_zero_iff.mpr hx
    simp
    exact_mod_cast Int.one_le_abs h3
  have hpos : ∀ φ : K →+* ℂ, 0 < ‖φ (x:K)‖ := fun φ => norm_pos_iff.mpr ((map_ne_zero φ).mpr hx')
  have hlog : 0 ≤ ∑ φ : K →+* ℂ, Real.log (‖φ (x:K)‖ ^ 2) := by
    rw [← Real.log_prod (fun φ _ => (pow_pos (hpos φ) 2).ne'), Finset.prod_pow]
    exact Real.log_nonneg (one_le_pow₀ hN)
  have : ∑ φ : K →+* ℂ, (1 + Real.log (‖φ (x:K)‖ ^ 2)) ≤ ∑ φ : K →+* ℂ, ‖φ (x:K)‖ ^ 2 :=
    Finset.sum_le_sum fun φ _ => by
      linarith [Real.add_one_le_exp (Real.log (‖φ (x:K)‖ ^ 2)), Real.exp_log (pow_pos (hpos φ) 2)]
  rw [Finset.sum_add_distrib] at this
  simp only [Finset.sum_const, Finset.card_univ, NumberField.Embeddings.card, nsmul_eq_mul, mul_one] at this
  linarith

theorem moduli_entry_bound : Ms_entry := by
  intro f p q z R2 hp hq hz hP hQ
  have h0 : 0 ≤ ∑ τ, p τ := Finset.sum_nonneg fun τ _ => hp τ
  have h0' : 0 ≤ ∑ τ, q τ := Finset.sum_nonneg fun τ _ => hq τ
  calc ∑ τ, ‖z τ‖ ^ 2 ≤ ∑ τ, p τ * q τ := Finset.sum_le_sum fun τ _ => hz τ
    _ ≤ ∑ τ, p τ * ∑ σ, q σ := Finset.sum_le_sum fun τ _ =>
        mul_le_mul_of_nonneg_left (Finset.single_le_sum (fun σ _ => hq σ) (Finset.mem_univ τ)) (hp τ)
    _ = (∑ τ, p τ) * ∑ σ, q σ := by rw [Finset.sum_mul]
    _ ≤ R2 * R2 := mul_le_mul hP hQ h0' (h0.trans hP)
    _ = R2 ^ 2 := by ring

theorem hadamard_unit_diagonal_det_le_one (N : ℕ) (H : Matrix (Fin N) (Fin N) ℂ) (hH : H.PosSemidef) (hd : ∀ c, H c c = 1) :
    H.det.re ≤ 1 := by
  have hh := hH.isHermitian
  have hdet := hh.det_eq_prod_eigenvalues
  have htr := hh.trace_eq_sum_eigenvalues
  have hnn := hH.eigenvalues_nonneg
  have htr' : ∑ i, hh.eigenvalues i = N := by
    have h1 : (H.trace) = (N : ℂ) := by simp [Matrix.trace, hd]
    rw [h1] at htr
    have h2 : ((N : ℝ) : ℂ) = ((∑ i, hh.eigenvalues i : ℝ) : ℂ) := by
      push_cast; simpa using htr
    exact_mod_cast h2.symm
  rw [hdet]
  have h3 : (∏ i, ((hh.eigenvalues i : ℝ) : ℂ)).re = ∏ i, hh.eigenvalues i := by
    rw [← Complex.ofReal_prod, Complex.ofReal_re]
  have h4 : (∏ i, (RCLike.ofReal (hh.eigenvalues i) : ℂ)).re = ∏ i, hh.eigenvalues i := by
    simpa using h3
  rw [h4]
  calc ∏ i, hh.eigenvalues i ≤ ∏ i, Real.exp (hh.eigenvalues i - 1) :=
        Finset.prod_le_prod (fun i _ => hnn i)
          (fun i _ => by linarith [Real.add_one_le_exp (hh.eigenvalues i - 1)])
    _ = Real.exp (∑ i, (hh.eigenvalues i - 1)) := (Real.exp_sum _ _).symm
    _ = 1 := by rw [Finset.sum_sub_distrib, htr']; simp

theorem hadamard_inequality_bound : Ms_hadamard := by
  intro N G hG
  have hdiag : ∀ c, 0 ≤ (G c c).re ∧ (G c c).im = 0 := by
    intro c
    have := hG.diag_nonneg (i := c)
    rw [Complex.le_def] at this
    exact ⟨by simpa using this.1, by simpa using this.2.symm⟩
  by_cases h0 : ∃ c, (G c c).re = 0
  · obtain ⟨c, hc⟩ := h0
    have hGc : G c c = 0 := Complex.ext hc (hdiag c).2
    have hv : G *ᵥ (Pi.single c 1) = 0 := by
      apply (hG.dotProduct_mulVec_zero_iff _).mp
      simp [hGc]
    have hdet : G.det = 0 :=
      Matrix.exists_mulVec_eq_zero_iff.mp ⟨Pi.single c 1, by simp, hv⟩
    rw [hdet, Finset.prod_eq_zero (mem_univ c) hc]; simp
  · push Not at h0
    have hpos : ∀ c, 0 < (G c c).re := fun c => lt_of_le_of_ne (hdiag c).1 (Ne.symm (h0 c))
    let s : Fin N → ℝ := fun c => (Real.sqrt (G c c).re)⁻¹
    have hs2 : ∀ c, s c * s c = ((G c c).re)⁻¹ := by
      intro c
      simp only [s]
      rw [← mul_inv, Real.mul_self_sqrt (hpos c).le]
    let Dg : Matrix (Fin N) (Fin N) ℂ := Matrix.diagonal (fun c => (s c : ℂ))
    have hDg : Dgᴴ = Dg := by
      simp [Dg, Matrix.diagonal_conjTranspose, Pi.star_def]
    have hH : (Dgᴴ * G * Dg).PosSemidef := hG.conjTranspose_mul_mul_same Dg
    rw [hDg] at hH
    have hGre : ∀ c, G c c = (((G c c).re : ℝ) : ℂ) := fun c => Complex.ext (by simp) (by simp [(hdiag c).2])
    have hHd : ∀ c, (Dg * G * Dg) c c = 1 := by
      intro c
      simp only [Dg, Matrix.mul_diagonal, Matrix.diagonal_mul]
      rw [hGre c]
      have : (s c : ℂ) * (((G c c).re : ℝ) : ℂ) * (s c : ℂ) = ((s c * s c * (G c c).re : ℝ) : ℂ) := by
        push_cast; ring
      rw [this, hs2 c, inv_mul_cancel₀ (hpos c).ne']; simp
    have h1 := hadamard_unit_diagonal_det_le_one N _ hH hHd
    have hdetD : Dg.det = ((∏ c, s c : ℝ) : ℂ) := by simp [Dg, Matrix.det_diagonal]
    rw [Matrix.det_mul, Matrix.det_mul, hdetD] at h1
    have h2 : (((∏ c, s c : ℝ) : ℂ) * G.det * ((∏ c, s c : ℝ) : ℂ)).re = ((∏ c, s c) * (∏ c, s c)) * G.det.re := by
      rw [Complex.re_mul_ofReal, Complex.re_ofReal_mul]; ring
    rw [h2, ← Finset.prod_mul_distrib] at h1
    simp only [hs2] at h1
    rw [Finset.prod_inv_distrib] at h1
    have hP : 0 < ∏ c, (G c c).re := Finset.prod_pos (fun c _ => hpos c)
    rwa [inv_mul_le_iff₀ hP, mul_one] at h1

theorem moduli_intermediate_bound : Ms_between := by
  intro R G _ _ _ _ r
  have : Nat.card (Fin r → G) = Nat.card G ^ r := by simp [Nat.card_fun]
  rw [← this]
  apply Nat.card_le_card_of_surjective (fun s : Fin r → G =>
    (⟨Submodule.span R (Set.range s), s, rfl⟩ :
      {H : Submodule R G // ∃ s : Fin r → G, Submodule.span R (Set.range s) = H}))
  rintro ⟨H, s, rfl⟩
  exact ⟨s, rfl⟩

theorem mean_value_inequality_radial : MeanValueInequalityRadial := by
  intro E _ _ _ _ _ μ _ F hF hinv hint
  let f : ℝ → E → ℝ := fun θ w => ‖F (Complex.exp (θ * Complex.I) • w)‖ ^ 2
  have hFc : Continuous F := hF.continuous
  have hcont : Continuous (Function.uncurry f) := by
    have : Function.uncurry f = fun p : ℝ × E => ‖F (Complex.exp (p.1 * Complex.I) • p.2)‖ ^ 2 := rfl
    rw [this]
    fun_prop
  have h2pi : (0:ℝ) ≤ 2 * π := by positivity
  have hpt : ∀ w : E, ‖F 0‖ ^ 2 ≤ (2 * π)⁻¹ * (∫ θ in (0:ℝ)..2 * π, f θ w) := by
    intro w
    let G : ℂ → ℂ := fun ζ => (F (ζ • w)) ^ 2
    have hG : Differentiable ℂ G := by
      have h1 : Differentiable ℂ (fun ζ : ℂ => ζ • w) := by fun_prop
      exact (hF.comp h1).pow 2
    have hmv : Real.circleAverage G 0 1 = G 0 := (hG.diffContOnCl).circleAverage
    have hG0 : ‖G 0‖ = ‖F 0‖ ^ 2 := by simp [G]
    rw [← hG0, ← hmv, Real.circleAverage_def, norm_smul, Real.norm_of_nonneg (by positivity)]
    gcongr
    refine (intervalIntegral.norm_integral_le_integral_norm h2pi).trans (le_of_eq ?_)
    refine intervalIntegral.integral_congr fun θ _ => ?_
    simp [G, f, circleMap]
  have hmeas : ∀ θ : ℝ, Measurable (fun w : E => Complex.exp (θ * Complex.I) • w) := fun θ =>
    (continuous_const_smul _).measurable
  have hsm : AEStronglyMeasurable (fun w => ‖F w‖ ^ 2) μ := hint.1
  have hslice_int : ∀ θ, Integrable (f θ) μ := by
    intro θ
    have h1 := hint
    rw [← hinv θ] at h1
    exact (integrable_map_measure (by rw [hinv θ]; exact hsm) (hmeas θ).aemeasurable).mp h1
  have hslice : ∀ θ, ∫ w, f θ w ∂μ = ∫ w, ‖F w‖ ^ 2 ∂μ := by
    intro θ
    conv_rhs => rw [← hinv θ]
    rw [integral_map (hmeas θ).aemeasurable (by rw [hinv θ]; exact hsm)]
  have hprod : Integrable (Function.uncurry f) ((volume.restrict (Set.uIoc 0 (2 * π))).prod μ) := by
    rw [integrable_prod_iff hcont.aestronglyMeasurable]
    refine ⟨Filter.Eventually.of_forall fun θ => hslice_int θ, ?_⟩
    have h1 : (fun θ => ∫ w, ‖Function.uncurry f (θ, w)‖ ∂μ) = fun _ => ∫ w, ‖F w‖ ^ 2 ∂μ := by
      funext θ
      rw [← hslice θ]
      refine integral_congr_ae (Filter.Eventually.of_forall fun w => ?_)
      simp [f]
    rw [h1, Set.uIoc_of_le h2pi]
    exact integrable_const _
  have hswap := intervalIntegral_integral_swap hprod
  have hI : Integrable (fun w => ∫ θ in (0:ℝ)..2 * π, f θ w) μ := by
    have h := hprod.integral_prod_right
    simpa [intervalIntegral.integral_of_le h2pi, Set.uIoc_of_le h2pi, Function.uncurry] using h
  calc ‖F 0‖ ^ 2 = ∫ _w, ‖F 0‖ ^ 2 ∂μ := by simp
    _ ≤ ∫ w, (2 * π)⁻¹ * (∫ θ in (0:ℝ)..2 * π, f θ w) ∂μ :=
        integral_mono (integrable_const _) (hI.const_mul _) hpt
    _ = (2 * π)⁻¹ * ∫ w, (∫ θ in (0:ℝ)..2 * π, f θ w) ∂μ := integral_const_mul _ _
    _ = (2 * π)⁻¹ * ∫ θ in (0:ℝ)..2 * π, (∫ w, f θ w ∂μ) := by rw [hswap]
    _ = (2 * π)⁻¹ * ∫ θ in (0:ℝ)..2 * π, (∫ w, ‖F w‖ ^ 2 ∂μ) := by simp_rw [hslice]
    _ = ∫ w, ‖F w‖ ^ 2 ∂μ := by
        rw [intervalIntegral.integral_const, sub_zero, smul_eq_mul, ← mul_assoc,
          inv_mul_cancel₀ (by positivity), one_mul]

theorem block_cauchy_schwarz : WeightedCauchySchwarz := by
  intro ι _ w q c O hw hO
  have h1 : ‖∑ e, q e * (w e : ℂ) * c e‖ ≤ ∑ e, (‖q e‖ * Real.sqrt (w e)) * (‖c e‖ * Real.sqrt (w e)) := by
    refine (norm_sum_le _ _).trans (le_of_eq (Finset.sum_congr rfl fun e _ => ?_))
    rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg (hw e).le]
    nth_rewrite 1 [← Real.mul_self_sqrt (hw e).le]
    ring
  have h2 := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun e => ‖q e‖ * Real.sqrt (w e))
    (fun e => ‖c e‖ * Real.sqrt (w e))
  have h3 : ∀ (x : ι → ℂ) e, (‖x e‖ * Real.sqrt (w e)) ^ 2 = ‖x e‖ ^ 2 * w e := by
    intro x e; rw [mul_pow, Real.sq_sqrt (hw e).le]
  simp only [h3] at h2
  have h4 : (∑ e, ‖q e‖ ^ 2 * w e) * O⁻¹ * ∑ e, ‖c e‖ ^ 2 * w e * O
      = (∑ e, ‖q e‖ ^ 2 * w e) * ∑ e, ‖c e‖ ^ 2 * w e := by
    rw [← Finset.sum_mul]; field_simp
  rw [h4]
  calc _ ≤ (∑ e, (‖q e‖ * Real.sqrt (w e)) * (‖c e‖ * Real.sqrt (w e))) ^ 2 := by gcongr
    _ ≤ _ := h2

theorem L1LeSqrtCardOfL2_statement : L1LeSqrtCardOfL2 := by
  intro ι _ c h
  apply Real.le_sqrt_of_sq_le
  have := sq_sum_le_card_mul_sum_sq (s := (univ : Finset ι)) (f := fun e => ‖c e‖)
  simp only [Finset.card_univ] at this
  nlinarith [Nat.cast_nonneg (α := ℝ) (Fintype.card ι)]

theorem third_zeta_minor_bound : UnitaryMinorNormLeOne := by
  intro n r U e e' hU
  by_cases he : Function.Injective e
  · have hG : ((U.submatrix e e')ᴴ * (U.submatrix e e')).PosSemidef :=
      Matrix.posSemidef_conjTranspose_mul_self _
    have h1 := hadamard_inequality_bound r _ hG
    have hdet : ((U.submatrix e e')ᴴ * (U.submatrix e e')).det.re = ‖(U.submatrix e e').det‖ ^ 2 := by
      rw [Matrix.det_mul, Matrix.det_conjTranspose, Complex.star_def, ← Complex.normSq_eq_conj_mul_self,
        Complex.normSq_eq_norm_sq, Complex.ofReal_re]
    have hentry : ∀ c, (((U.submatrix e e')ᴴ * (U.submatrix e e')) c c).re = ∑ a, ‖U (e a) (e' c)‖ ^ 2 := by
      intro c
      simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.submatrix_apply, Complex.re_sum]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [Complex.star_def, ← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq, Complex.ofReal_re]
    have hUU : ∀ j, ∑ i, ‖U i j‖ ^ 2 = 1 := by
      intro j
      have h3 : (Uᴴ * U) j j = 1 := by
        have := (Matrix.mem_unitaryGroup_iff').mp hU
        rw [Matrix.star_eq_conjTranspose] at this
        rw [this]; simp
      have h4 : ((Uᴴ * U) j j).re = ∑ i, ‖U i j‖ ^ 2 := by
        simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Complex.re_sum]
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [Complex.star_def, ← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq, Complex.ofReal_re]
      rw [← h4, h3]; simp
    have hcol : ∀ c, (((U.submatrix e e')ᴴ * (U.submatrix e e')) c c).re ≤ 1 := by
      intro c
      rw [hentry c, ← hUU (e' c)]
      calc ∑ a, ‖U (e a) (e' c)‖ ^ 2 = ∑ i ∈ Finset.univ.image e, ‖U i (e' c)‖ ^ 2 := by
            rw [Finset.sum_image (fun a _ b _ h => he h)]
        _ ≤ ∑ i, ‖U i (e' c)‖ ^ 2 :=
            Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun _ _ _ => by positivity)
    have hcol0 : ∀ c, 0 ≤ (((U.submatrix e e')ᴴ * (U.submatrix e e')) c c).re := by
      intro c; rw [hentry c]; positivity
    have h5 : ‖(U.submatrix e e').det‖ ^ 2 ≤ 1 := by
      rw [← hdet]
      exact h1.trans (Finset.prod_le_one (fun c _ => hcol0 c) (fun c _ => hcol c))
    exact (sq_le_one_iff₀ (norm_nonneg _)).mp h5
  · obtain ⟨a, b, hab, hne⟩ : ∃ a b, e a = e b ∧ a ≠ b := by
      simpa [Function.Injective] using he
    have : (U.submatrix e e').det = 0 :=
      Matrix.det_zero_of_row_eq hne (by ext j; simp [hab])
    simp [this]

theorem inverse_norm_le_of_integer_inner : InverseNormLeOfIntegerInner := by
  intro V _ _ x φ z hz h
  have h1 : (1:ℝ) ≤ ‖inner ℂ x φ‖ := by
    rw [h, Complex.norm_intCast]; exact_mod_cast Int.one_le_abs hz
  have h2 := norm_inner_le_norm (𝕜 := ℂ) x φ
  have hx : 0 < ‖x‖ := by
    rcases (norm_nonneg x).lt_or_eq with h' | h'
    · exact h'
    · rw [← h'] at h2; linarith
  rw [div_le_iff₀ hx]; linarith [mul_comm ‖x‖ ‖φ‖]

theorem third_zeta_arithmetic_bound : InterlacingLogSquareBound := by
  intro n lam nu T c rho hI hT hc hcb hr hrb
  have hT0 : 0 < T := by linarith
  have hz : 0 < T ^ (-(degZ lam nu)) := zpow_pos hT0 _
  have hd : 0 < weylDim lam := (mul_pos_iff_of_pos_left hz).1 (lt_of_lt_of_le (by positivity) hrb)
  have hmin : ∀ i, 0 ≤ min (len lam i) (B0 lam nu) := by
    intro i
    refine le_min ?_ ?_
    · unfold len; have := hI.1 (Fin.castSucc_le_succ i); linarith
    · unfold B0; exact Finset.sum_nonneg fun j _ => by have := (hI.2 j).1; linarith
  have hsum : ((∑ i, (min (len lam i) (B0 lam nu)).toNat : ℕ) : ℝ)
      = ∑ i, ((min (len lam i) (B0 lam nu) : ℤ) : ℝ) := by
    push_cast
    refine Finset.sum_congr rfl fun i _ => ?_
    have := Int.toNat_of_nonneg (hmin i)
    exact_mod_cast this
  have e1 : Real.log ((c * rho) ^ 2) = 2 * Real.log |c| + Real.log (rho ^ 2) := by
    rw [mul_pow, Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_abs]; push_cast; ring
  have e2 : Real.log |c| ≤ ((n * ∑ i, (min (len lam i) (B0 lam nu)).toNat : ℕ) : ℝ) * Real.log (Wnum lam : ℝ) := by
    have := Real.log_le_log (abs_pos.2 hc) hcb
    rwa [Real.log_pow] at this
  have e3 : Real.log (rho ^ 2) ≤ -(degZ lam nu : ℝ) * Real.log T + Real.log (weylDim lam) := by
    have := Real.log_le_log (by positivity) hrb
    rw [Real.log_mul hz.ne' hd.ne', Real.log_zpow] at this
    push_cast at this; exact this
  rw [Nat.cast_mul, hsum] at e2
  unfold MeanSquareTwistBound
  rw [e1]; nlinarith

theorem weight_positive_part_nonneg {κ : ℕ} (lam : Fin (κ + 1) → ℤ) (h : Antitone lam) : 0 ≤ wt (plus lam) := by
  unfold wt plus
  exact Finset.sum_nonneg fun i _ => by have := h (Fin.le_last i); linarith

theorem fourth_zeta_arithmetic_bound : MuMaxBoundOfAntitoneWeight := by
  intro κ lam muMax dmin cc hA hcc hd hdm hc hmu
  have hk : (0:ℝ) < (κ : ℝ) + 1 := by positivity
  have hw := weight_positive_part_nonneg lam hA
  have e1 : -Real.log dmin ≤ (wt (plus lam) : ℝ) * Real.log ((κ : ℝ) + 1) := by
    have := Real.log_le_log (by positivity) hdm
    rw [Real.log_inv, Real.log_pow] at this
    have h2 : (((wt (plus lam)).toNat : ℕ) : ℝ) = (wt (plus lam) : ℝ) := by
      exact_mod_cast Int.toNat_of_nonneg hw
    rw [h2] at this; linarith
  have e2 : Real.log cc ≤ ((κ : ℝ) + 1) ^ 2 * Real.log ((plus lam 0 : ℝ) + (κ : ℝ) + 1) := by
    have := Real.log_le_log hcc hc
    rw [Real.log_pow] at this
    push_cast at this; exact this
  unfold MeanSquareWeightBound; linarith

theorem fifth_zeta_arithmetic_bound : AntitoneWeightLogBoundExists := by
  intro C₀ hC
  refine ⟨Real.log C₀ / Real.log 2 + 4, ?_⟩
  intro κ lam v logT logNorm muStd mu hv hT hA hN hS hmu
  rcases Nat.eq_zero_or_pos κ with rfl | hκ
  · have w0 : wt (plus lam) = 0 := by simp [wt, plus]
    have p0 : plus lam 0 = 0 := by simp [plus]
    have z0 : MeanSquareWeightBound lam = 0 := by simp [MeanSquareWeightBound, w0, p0]
    rw [w0] at hmu ⊢
    rw [p0]
    rw [z0] at hS
    have : -(lam (Fin.last 0) : ℝ) * logT ≤ |(lam (Fin.last 0) : ℝ)| * logT :=
      mul_le_mul_of_nonneg_right (neg_le_abs _) hT
    simp at hmu this ⊢
    linarith
  · have hκ' : (1:ℝ) ≤ κ := by exact_mod_cast hκ
    have hk : (2:ℝ) ≤ (κ : ℝ) + 1 := by linarith
    have hw : (0:ℝ) ≤ (wt (plus lam) : ℝ) := by exact_mod_cast weight_positive_part_nonneg lam hA
    have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have hlk : Real.log 2 ≤ Real.log ((κ : ℝ) + 1) := Real.log_le_log (by norm_num) hk
    have hlv : 0 ≤ Real.log v := Real.log_nonneg hv
    have hlC : 0 ≤ Real.log C₀ := Real.log_nonneg hC
    have ekv : Real.log (((κ : ℝ) + 1) * v) = Real.log ((κ : ℝ) + 1) + Real.log v :=
      Real.log_mul (by positivity) (by positivity)
    have eN : Real.log (C₀ * ((κ : ℝ) + 1) ^ 3 * v ^ 2)
        = Real.log C₀ + 3 * Real.log ((κ : ℝ) + 1) + 2 * Real.log v := by
      rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
        Real.log_pow, Real.log_pow]; push_cast; ring
    have h1 : Real.log C₀ ≤ Real.log C₀ / Real.log 2 * Real.log (((κ : ℝ) + 1) * v) := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hl2]
      exact mul_le_mul_of_nonneg_left (by rw [ekv]; linarith) hlC
    have h2 : logNorm + Real.log ((κ : ℝ) + 1) ≤ (Real.log C₀ / Real.log 2 + 4) * Real.log (((κ : ℝ) + 1) * v) := by
      rw [eN] at hN
      have : (Real.log C₀ / Real.log 2 + 4) * Real.log (((κ : ℝ) + 1) * v)
        = Real.log C₀ / Real.log 2 * Real.log (((κ : ℝ) + 1) * v) + 4 * (Real.log ((κ : ℝ) + 1) + Real.log v) := by
        rw [← ekv]; ring
      rw [this]; linarith
    have h3 := mul_le_mul_of_nonneg_left h2 hw
    have h4 : -(lam (Fin.last κ) : ℝ) * logT ≤ |(lam (Fin.last κ) : ℝ)| * logT :=
      mul_le_mul_of_nonneg_right (neg_le_abs _) hT
    unfold MeanSquareWeightBound at hS
    nlinarith

theorem column_other_entries : Col_other := by
  intro κ lam S hS hl h0 hm
  unfold wt plus
  rw [Fin.sum_univ_succ]
  have : ∑ i : Fin κ, (lam i.succ - lam (Fin.last κ)) ≤ ∑ _i : Fin κ, (S + 1) :=
    Finset.sum_le_sum fun i _ => hm _ (Fin.succ_ne_zero i)
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at this
  nlinarith

end Formalism.HermitianLattices.LatticeEstimates
