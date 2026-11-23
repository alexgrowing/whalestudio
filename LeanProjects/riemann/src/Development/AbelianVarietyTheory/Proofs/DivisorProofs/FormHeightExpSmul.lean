import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.AevalEqZeroOfMemConeIdeal

set_option autoImplicit false

noncomputable section

open MvPolynomial NumberField Module GlobalTheory.ChowHt GlobalTheory.CompHt MeasureTheory ReciprocityTheory.MultiplicativeHeights

namespace GlobalTheory.HeightShift

theorem linSubst_smul {R : Type} [CommRing R] {B N n m : ℕ} (s : R) (M : Matrix (Fin N) (Fin n) R)
    {g : MvPolynomial (Fin B × Fin N) R} (hg : g.IsHomogeneous m) :
    linSubst (s • M) g = C (s ^ m) * linSubst M g := by
  conv_lhs => rw [g.as_sum]
  conv_rhs => rw [g.as_sum]
  simp only [linSubst, map_sum, aeval_monomial, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a ha => ?_
  have : a.degree = m := by rw [Finsupp.degree_eq_weight_one]; exact hg (mem_support_iff.1 ha)
  simp only [Matrix.smul_apply, smul_eq_mul, map_mul, mul_assoc, ← Finset.mul_sum, Finsupp.prod, mul_pow,
    Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, map_pow]
  rw [← this, Finsupp.degree_apply, mul_left_comm]

theorem blockSphereMean_C {B n : ℕ} (hn : 0 < n) (c : ℂ) :
    blockSphereMean B n (C c) = Real.log ‖c‖ := by
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
  simp [MvPolynomial.eval_C]

theorem frameNorm_exp_smul {N : ℕ} {A : Matrix (Fin N) (Fin N) ℂ} (hA : A.det ≠ 0) (t : ℝ) (x : Fin N → ℂ) :
    frameNorm (((Real.exp t : ℝ) : ℂ) • A) x = Real.exp (-t) * frameNorm A x := by
  have h : (((Real.exp t : ℝ) : ℂ) • A)⁻¹ = ((Real.exp (-t) : ℝ) : ℂ) • A⁻¹ := by
    refine Matrix.inv_eq_right_inv ?_
    rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, A.mul_nonsing_inv hA.isUnit, ← Complex.ofReal_mul,
      ← Real.exp_add, add_neg_cancel, Real.exp_zero, Complex.ofReal_one, one_smul]
  rw [frameNorm, frameNorm, h, Matrix.smul_mulVec]
  simp only [Pi.smul_apply, smul_eq_mul, norm_mul, mul_pow, ← Finset.mul_sum, Complex.norm_real,
    Real.norm_of_nonneg (Real.exp_pos _).le]
  rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (Real.exp_pos _).le]

theorem formHeight_exp_smul {F : Type} [Field F] [NumberField F] {B N n : ℕ} (hN : 0 < N) (δ : ℕ)
    (w : Matrix (Fin N) (Fin n) F) {A : (F →+* ℂ) → Matrix (Fin N) (Fin N) ℂ} (hA : ∀ σ, (A σ).det ≠ 0)
    {f : MvPolynomial (Fin B × Fin N) F} (hf : f ≠ 0) (ha : IsMultiHomogeneous (fun _ => δ) f)
    (t : (F →+* ℂ) → ℝ) :
    formHeight δ w (fun σ => ((Real.exp (t σ) : ℝ) : ℂ) • A σ) f =
      formHeight δ w A f + (B : ℝ) * δ * ((∑ σ, t σ) / (finrank ℚ F : ℝ)) := by
  have hinf : ∀ σ : F →+* ℂ,
      blockSphereMean B N (linSubst (((Real.exp (t σ) : ℝ) : ℂ) • A σ) (MvPolynomial.map σ f)) =
      (B : ℝ) * δ * t σ + blockSphereMean B N (linSubst (A σ) (MvPolynomial.map σ f)) := by
    intro σ
    have hm := isMultiHomogeneous_map_ring _ f ha σ
    have hh := (isMultiHomogeneous_iff_block.1 hm).isHomogeneous
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at hh
    have hs : ((Real.exp (t σ) : ℝ) : ℂ) ^ (B * δ) ≠ 0 :=
      pow_ne_zero _ (Complex.ofReal_ne_zero.2 (Real.exp_pos _).ne')
    rw [linSubst_smul _ _ hh, sphere_mean_mul_multihomogeneous Closed.sphereLogIntegrable B N 0 (fun _ => δ) _ _
      (by rwa [Ne, MvPolynomial.C_eq_zero])
      (HeightUnique.linSubst_ne_zero ((A σ).mul_nonsing_inv (hA σ).isUnit) fun h => hf
        (MvPolynomial.map_injective σ σ.injective (by rw [h, map_zero])))
      (isMultiHomogeneous_iff_block.2 (isWeightedHomogeneous_C _ _)) (HeightUnique.linSubst_homog _ hm),
      blockSphereMean_C hN, norm_pow, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le,
      Real.log_pow, Real.log_exp, Nat.cast_mul]
  unfold formHeight
  simp only [hinf, Finset.sum_add_distrib, ← Finset.mul_sum]
  ring

theorem isImageHeight_shift : ∀ (K V Ω : Type) [Field K] [NumberField K] [AddCommGroup V] [Module K V]
    [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [Field Ω] [Algebra K Ω] (Nm : (K →+* ℂ) → V → ℝ)
    (L : Submodule (𝓞 K) V) (ev : V →ₗ[K] Ω) (D : ℕ) (h : ℝ), ∀ t : (K →+* ℂ) → ℝ,
    (∀ σ, t ((starRingEnd ℂ).comp σ) = t σ) → IsImageHeight Nm L ev D h →
    IsImageHeight (fun σ x => Real.exp (-t σ) * Nm σ x) L ev D (h + (∑ σ, t σ) / (finrank ℚ K : ℝ)) := by
  rintro K V Ω _ _ _ _ _ _ _ _ Nm L ev D h t ht ⟨N, n, b, w, A, δ, f, hF, hf, e⟩
  obtain ⟨y, hy, -⟩ := hf.exists_point
  obtain ⟨j, -⟩ := Function.ne_iff.1 hy
  refine ⟨N, n, b, w, fun σ => ((Real.exp (t σ) : ℝ) : ℂ) • A σ, δ, f,
    ⟨hF.span, hF.full, fun σ => ?_, fun σ x => ?_, fun σ x => ?_⟩, hf, ?_⟩
  · rw [Matrix.det_smul]
    exact mul_ne_zero (pow_ne_zero _ (Complex.ofReal_ne_zero.2 (Real.exp_pos _).ne')) (hF.herm σ)
  · simp only [frameNorm_exp_smul (hF.herm _), ht]
    rw [hF.conj σ x]
  · rw [frameNorm_exp_smul (hF.herm _), hF.norm]
  · rw [formHeight_exp_smul (Fin.pos j) δ w hF.herm hf.ne_zero hf.homog, ← e]
    push_cast
    ring

end GlobalTheory.HeightShift
