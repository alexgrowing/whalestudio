import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.AevalEqZeroOfMemConeIdeal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BlockSphereMeanEqOfFrameNormEq

set_option autoImplicit false

noncomputable section

open MvPolynomial NumberField MeasureTheory GlobalTheory.ChowHt GlobalTheory.HeightUnique ReciprocityTheory.MultiplicativeHeights

namespace PositivityTheory.UnitarySelfGeneration.FrameHeightScaling

theorem linSubst_smul {B N δ : ℕ} (c : ℂ) (A : Matrix (Fin N) (Fin N) ℂ) {f : MvPolynomial (Fin B × Fin N) ℂ}
    (hf : IsMultiHomogeneous (fun _ => δ) f) : linSubst (c • A) f = C (c ^ (B * δ)) * linSubst A f := by
  refine MvPolynomial.funext fun u => ?_
  rw [map_mul, eval_C, GlobalTheory.SphereMeanFrame.eval_linSubst, GlobalTheory.SphereMeanFrame.eval_linSubst, eval_eq', eval_eq',
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun s hs => ?_
  have h1 : ∑ p, s p = B * δ := by
    rw [Fintype.sum_prod_type, Finset.sum_congr rfl fun b _ => hf s hs b]
    simp
  have h2 : ∀ p : Fin B × Fin N, ∑ k, (c • A) p.2 k * u (p.1, k) = c * ∑ k, A p.2 k * u (p.1, k) := fun p => by
    simp only [Matrix.smul_apply, smul_eq_mul, Finset.mul_sum, mul_assoc]
  simp only [h2, mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, h1]
  ring

theorem blockSphereMean_C {B n : ℕ} (hn : 0 < n) (z : ℂ) :
    blockSphereMean B n (C z) = Real.log ‖z‖ := by
  have hP : IsProbabilityMeasure (blockSphereProb B n) := by
    have : NeZero n := ⟨hn.ne'⟩
    have hne : (volume : Measure (EuclideanSpace ℂ (Fin n))).toSphere Set.univ ≠ 0 := by
      rw [Ne, Measure.measure_univ_eq_zero]
      exact Measure.toSphere_ne_zero _
    have : IsProbabilityMeasure (sphereProb n) := by
      unfold sphereProb
      exact ProbabilityTheory.cond_isProbabilityMeasure hne
    unfold blockSphereProb
    infer_instance
  unfold blockSphereMean
  simp

theorem formHeight_smul {F : Type} [Field F] [NumberField F] {B N n δ : ℕ} (hN : 0 < N)
    (w : Matrix (Fin N) (Fin n) F) {A : (F →+* ℂ) → Matrix (Fin N) (Fin N) ℂ} (hA : ∀ σ, (A σ).det ≠ 0)
    {f : MvPolynomial (Fin B × Fin N) F} (hf : f ≠ 0) (ha : IsMultiHomogeneous (fun _ => δ) f) (r : ℝ) :
    formHeight δ w (fun σ => ((Real.exp r : ℝ) : ℂ) • A σ) f = formHeight δ w A f + B * δ * r := by
  have hd : (Module.finrank ℚ F : ℝ) ≠ 0 := Nat.cast_ne_zero.2 Module.finrank_pos.ne'
  have hc : ((Real.exp r : ℝ) : ℂ) ^ (B * δ) ≠ 0 := pow_ne_zero _ (Complex.ofReal_ne_zero.2 (Real.exp_pos r).ne')
  have hinf : ∀ σ : F →+* ℂ, blockSphereMean B N (linSubst (((Real.exp r : ℝ) : ℂ) • A σ) (MvPolynomial.map σ f)) =
      B * δ * r + blockSphereMean B N (linSubst (A σ) (MvPolynomial.map σ f)) := by
    intro σ
    have hm := isMultiHomogeneous_map_ring _ f ha σ
    rw [linSubst_smul _ _ hm, sphere_mean_mul_multihomogeneous Closed.sphereLogIntegrable B N 0 _ _ _
      (by rwa [Ne, MvPolynomial.C_eq_zero])
      (linSubst_ne_zero ((A σ).mul_nonsing_inv (hA σ).isUnit) fun h =>
        hf (MvPolynomial.map_injective σ σ.injective (by rw [h, map_zero])))
      (isMultiHomogeneous_iff_block.2 (isWeightedHomogeneous_C _ _)) (linSubst_homog _ hm), blockSphereMean_C hN,
      norm_pow, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos r).le, Real.log_pow, Real.log_exp]
    push_cast
    ring
  unfold formHeight
  simp only [hinf, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, NumberField.Embeddings.card,
    nsmul_eq_mul]
  field_simp
  ring

theorem frameNorm_smul {N : ℕ} {A : Matrix (Fin N) (Fin N) ℂ} (hA : A.det ≠ 0) {c : ℂ} (hc : c ≠ 0)
    (x : Fin N → ℂ) : frameNorm (c • A) x = ‖c⁻¹‖ * frameNorm A x := by
  have h : (c • A)⁻¹ = c⁻¹ • A⁻¹ := Matrix.inv_eq_left_inv (by
    rw [smul_mul_smul_comm, inv_mul_cancel₀ hc, one_smul, Matrix.nonsing_inv_mul _ hA.isUnit])
  simp only [frameNorm, h, Matrix.smul_mulVec, Pi.smul_apply, smul_eq_mul, norm_mul, mul_pow, ← Finset.mul_sum]
  rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (norm_nonneg _)]

theorem conjCompat_smul {F : Type} [Field F] {N : ℕ} {A : (F →+* ℂ) → Matrix (Fin N) (Fin N) ℂ}
    (hA : ∀ σ, (A σ).det ≠ 0) (h : ConjCompat A) {c : ℂ} (hc : c ≠ 0) : ConjCompat fun σ => c • A σ := fun σ x => by
  rw [frameNorm_smul (hA _) hc, frameNorm_smul (hA _) hc, h σ x]

theorem sum_smul {m : ℕ} (M : Matrix (Fin m) (Fin m) ℂ) (c : ℂ) (v : Fin m → ℂ) :
    ∑ a, ‖∑ k, (c • M) k a * v k‖ ^ 2 = ‖c‖ ^ 2 * ∑ a, ‖∑ k, M k a * v k‖ ^ 2 := by
  simp only [Matrix.smul_apply, smul_eq_mul, mul_assoc, ← Finset.mul_sum, norm_mul, mul_pow]

theorem archSize_smul_sq {N : ℕ} (A : Matrix (Fin N) (Fin N) ℂ) (c : ℂ) (x : Fin N → ℂ) :
    GlobalTheory.Adelic.archSize (c • A) x ^ 2 = ‖c‖ ^ 2 * GlobalTheory.Adelic.archSize A x ^ 2 := by
  rw [GlobalTheory.Adelic.archSize, GlobalTheory.Adelic.archSize, Real.sq_sqrt (by positivity), Real.sq_sqrt (by positivity), sum_smul]

theorem log_step {m : ℕ} (M : Matrix (Fin m) (Fin m) ℂ) (r : ℝ) {c : ℂ} (hc : c ≠ 0) (v : Fin m → ℂ)
    (h : 0 < ∑ a, ‖∑ k, (((Real.exp r : ℝ) : ℂ) • M) k a * v k‖ ^ 2) :
    Real.log (∑ a, ‖∑ k, M k a * (c * v k)‖ ^ 2) + 2 * r =
      Real.log (∑ a, ‖∑ k, (((Real.exp r : ℝ) : ℂ) • M) k a * v k‖ ^ 2) + Real.log (‖c‖ ^ 2) := by
  have e : ∑ a, ‖∑ k, M k a * (c * v k)‖ ^ 2 = ‖c‖ ^ 2 * ∑ a, ‖∑ k, M k a * v k‖ ^ 2 := by
    rw [← sum_smul]
    simp only [Matrix.smul_apply, smul_eq_mul, mul_assoc, mul_left_comm c]
  rw [sum_smul] at h ⊢
  have h0 : ∑ a, ‖∑ k, M k a * v k‖ ^ 2 ≠ 0 := fun h0 => by rw [h0, mul_zero] at h; exact lt_irrefl _ h
  have h1 : ‖c‖ ^ 2 ≠ 0 := pow_ne_zero _ (norm_ne_zero_iff.2 hc)
  rw [e, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos r).le, Real.log_mul h1 h0,
    Real.log_mul (pow_ne_zero _ (Real.exp_pos r).ne') h0, Real.log_pow (Real.exp r), Real.log_exp]
  push_cast
  ring

end PositivityTheory.UnitarySelfGeneration.FrameHeightScaling
