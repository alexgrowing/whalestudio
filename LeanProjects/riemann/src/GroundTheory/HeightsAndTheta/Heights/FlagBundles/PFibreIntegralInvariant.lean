import Mathlib
import GroundTheory.HeightsAndTheta.Heights.FlagBundles.Statements
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FlagBundles

open MvPolynomial MeasureTheory
open scoped InnerProductSpace Pointwise

noncomputable section

namespace FibreIntegralInvariant

theorem eval_smul_of_isHomogeneous {σ : Type*} {φ : MvPolynomial σ ℝ} {n : ℕ}
    (h : φ.IsHomogeneous n) (s : ℝ) (x : σ → ℝ) : eval (s • x) φ = s ^ n * eval x φ := by
  classical
  conv_lhs => rw [φ.as_sum]
  conv_rhs => rw [φ.as_sum]
  simp only [map_sum, eval_monomial, Finset.mul_sum]
  refine Finset.sum_congr rfl fun d hd => ?_
  have hdeg : ∑ i ∈ d.support, d i = n := by
    have := h (mem_support_iff.mp hd)
    simpa [Finsupp.weight_apply, Finsupp.sum] using this
  simp only [Finsupp.prod, Pi.smul_apply, smul_eq_mul, mul_pow, Finset.prod_mul_distrib,
    Finset.prod_pow_eq_pow_sum, hdeg]
  ring

theorem gKernel_isHomogeneous (k : ℕ) : (gKernel ℝ k).IsHomogeneous (2 * k) := by
  unfold gKernel
  refine IsHomogeneous.sum _ _ _ fun j hj => ?_
  have hj : j < k := Finset.mem_range.mp hj
  refine IsHomogeneous.sub ?_ ?_
  · have := (isHomogeneous_X_pow (R := ℝ) (0 : Fin 2) (2 * j + 1)).mul
      (isHomogeneous_X_pow (R := ℝ) (1 : Fin 2) (2 * k - 1 - 2 * j))
    have e : 2 * j + 1 + (2 * k - 1 - 2 * j) = 2 * k := by omega
    rw [e] at this
    exact this
  · have := (isHomogeneous_X_pow (R := ℝ) (0 : Fin 2) (2 * j)).mul
      (isHomogeneous_X_pow (R := ℝ) (1 : Fin 2) (2 * k - 2 * j))
    have e : 2 * j + (2 * k - 2 * j) = 2 * k := by omega
    rw [e] at this
    exact this

theorem gMixed_isHomogeneous (k : ℕ) : (gMixed k).IsHomogeneous (2 * k - 2) := by
  have := ((gKernel_isHomogeneous k).pderiv (i := 1)).pderiv (i := 0)
  rw [Nat.sub_sub] at this
  exact this

theorem gMixed_one : gMixed 1 = 1 := by
  simp [gMixed, gKernel, Derivation.leibniz, Derivation.leibniz_pow, pderiv_X]
  rw [← map_ofNat (C : ℝ →+* MvPolynomial (Fin 2) ℝ) 2, pderiv_C]

def sphereMap (R : E3 ≃ₗᵢ[ℝ] E3) (n : Sphere2) : Sphere2 :=
  ⟨R n, by simp⟩

@[simp] theorem sphereMap_coe (R : E3 ≃ₗᵢ[ℝ] E3) (n : Sphere2) :
    (sphereMap R n : E3) = R n := rfl

theorem continuous_sphereMap (R : E3 ≃ₗᵢ[ℝ] E3) : Continuous (sphereMap R) :=
  (R.continuous.comp continuous_subtype_val).subtype_mk _

def sphereHomeo (R : E3 ≃ₗᵢ[ℝ] E3) : Sphere2 ≃ₜ Sphere2 where
  toFun := sphereMap R
  invFun := sphereMap R.symm
  left_inv n := by ext1; simp
  right_inv n := by ext1; simp
  continuous_toFun := continuous_sphereMap R
  continuous_invFun := continuous_sphereMap R.symm

theorem toSphere_map (R : E3 ≃ₗᵢ[ℝ] E3) :
    ((volume : Measure E3).toSphere).map (sphereMap R) = (volume : Measure E3).toSphere := by
  have hm : Measurable (sphereMap R) := (continuous_sphereMap R).measurable
  ext s hs
  rw [Measure.map_apply hm hs, Measure.toSphere_apply' volume (hm hs),
    Measure.toSphere_apply' volume hs]
  congr 1
  have himg : ((↑) '' (sphereMap R ⁻¹' s) : Set E3) = R ⁻¹' ((↑) '' s) := by
    ext x
    constructor
    · rintro ⟨n, hn, rfl⟩
      exact ⟨sphereMap R n, hn, rfl⟩
    · rintro ⟨m, hm', hx⟩
      have hxs : x ∈ Metric.sphere (0 : E3) 1 := by
        have h2 := m.2
        rw [hx, mem_sphere_zero_iff_norm, LinearIsometryEquiv.norm_map] at h2
        exact mem_sphere_zero_iff_norm.mpr h2
      refine ⟨⟨x, hxs⟩, ?_, rfl⟩
      have hme : sphereMap R ⟨x, hxs⟩ = m := Subtype.ext hx.symm
      simpa [Set.mem_preimage, hme] using hm'
  have hsmul : (Set.Ioo (0 : ℝ) 1 • (R ⁻¹' ((↑) '' s)) : Set E3) =
      R ⁻¹' (Set.Ioo (0 : ℝ) 1 • ((↑) '' s)) := by
    ext x
    simp only [Set.mem_preimage, Set.mem_smul]
    constructor
    · rintro ⟨c, hc, y, hy, rfl⟩
      exact ⟨c, hc, R y, hy, by simp⟩
    · rintro ⟨c, hc, y, hy, hxy⟩
      refine ⟨c, hc, R.symm y, by simpa using hy, ?_⟩
      apply R.injective
      simp [hxy]
  rw [himg, hsmul]
  exact (LinearIsometryEquiv.measurePreserving R).measure_preimage_equiv (f := R.toMeasurableEquiv) _

instance : IsProbabilityMeasure sphereMeasure := ⟨sphereMeasure_univ⟩

theorem measurePreserving_sphereMap (R : E3 ≃ₗᵢ[ℝ] E3) :
    MeasurePreserving (sphereMap R) sphereMeasure sphereMeasure := by
  refine ⟨(continuous_sphereMap R).measurable, ?_⟩
  rw [sphereMeasure, Measure.map_smul, toSphere_map]

theorem measurePreserving_pair (R : E3 ≃ₗᵢ[ℝ] E3) :
    MeasurePreserving (Prod.map (sphereMap R) (sphereMap R)) pairMeasure pairMeasure :=
  (measurePreserving_sphereMap R).prod (measurePreserving_sphereMap R)

theorem measurableEmbedding_pair (R : E3 ≃ₗᵢ[ℝ] E3) :
    MeasurableEmbedding (Prod.map (sphereMap R) (sphereMap R)) :=
  ((sphereHomeo R).prodCongr (sphereHomeo R)).measurableEmbedding

theorem exists_isometry (a : E3) :
    ∃ R : E3 ≃ₗᵢ[ℝ] E3, a = ‖a‖ • R (EuclideanSpace.single 2 1) := by
  by_cases ha : a = 0
  · exact ⟨LinearIsometryEquiv.refl ℝ E3, by simp [ha]⟩
  · have hn : ‖a‖ ≠ 0 := norm_ne_zero_iff.mpr ha
    have hu : ‖(EuclideanSpace.single 2 1 : E3)‖ = ‖‖a‖⁻¹ • a‖ := by
      rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hn]
      simp
    refine ⟨Submodule.reflection (ℝ ∙ ((EuclideanSpace.single 2 1 : E3) - ‖a‖⁻¹ • a))ᗮ, ?_⟩
    rw [Submodule.reflection_sub hu, smul_smul, mul_inv_cancel₀ hn, one_smul]

theorem mean_eq (k : ℕ) (a : E3) :
    ∫ p, kernelL ⟪(p.1 : E3), (p.2 : E3)⟫_ℝ *
        eval ![⟪a, (p.1 : E3)⟫_ℝ, ⟪a, (p.2 : E3)⟫_ℝ] (gMixed k) ∂pairMeasure =
      fibreConstant k * ⟪a, a⟫_ℝ ^ (k - 1) := by
  obtain ⟨R, hR⟩ := exists_isometry a
  have key : ∀ n : Sphere2, ⟪a, R (n : E3)⟫_ℝ = ‖a‖ * height n := by
    intro n
    conv_lhs => rw [hR]
    rw [real_inner_smul_left, LinearIsometryEquiv.inner_map_map]
    simp [height, EuclideanSpace.inner_single_left]
  have hvec : ∀ x y : ℝ, ![‖a‖ * x, ‖a‖ * y] = ‖a‖ • ![x, y] := by
    intro x y
    ext i
    fin_cases i <;> simp
  rw [← (measurePreserving_pair R).integral_comp (measurableEmbedding_pair R)]
  simp only [Prod.map_fst, Prod.map_snd, sphereMap_coe, LinearIsometryEquiv.inner_map_map, key,
    hvec, eval_smul_of_isHomogeneous (gMixed_isHomogeneous k)]
  have hpow : ⟪a, a⟫_ℝ ^ (k - 1) = ‖a‖ ^ (2 * k - 2) := by
    rw [real_inner_self_eq_norm_sq, ← pow_mul]
    congr 1
    omega
  rw [hpow, fibreConstant, ← integral_mul_const]
  congr 1
  ext p
  ring

def coordC (r : Fin 2) (i : Fin 3) : C(Sphere2 × Sphere2, ℝ) :=
  ⟨fun p => ((if r = 0 then p.1 else p.2 : Sphere2) : E3) i,
    (EuclideanSpace.proj i).continuous.comp (continuous_subtype_val.comp
      (continuous_if_const _ (fun _ => continuous_fst) (fun _ => continuous_snd)))⟩

def fibreQ (k : ℕ) : MvPolynomial (Fin 3) (Sphere2 × Sphere2 → ℝ) :=
  aeval (fun r : Fin 2 => ∑ i : Fin 3,
      X i * C (fun p : Sphere2 × Sphere2 => ((if r = 0 then p.1 else p.2 : Sphere2) : E3) i))
    (gMixed k)

theorem fibrePoly_eq (k : ℕ) : fibrePoly k = ∑ μ ∈ (fibreQ k).support,
    monomial μ (∫ p, kernelL ⟪(p.1 : E3), (p.2 : E3)⟫_ℝ * coeff μ (fibreQ k) p ∂pairMeasure) :=
  rfl

theorem fibreQ_eq_map (k : ℕ) : fibreQ k = mapAlgHom (ContinuousMap.coeFnAlgHom (R := ℝ))
    (aeval (fun r : Fin 2 => ∑ i : Fin 3, X i * C (coordC r i)) (gMixed k)) := by
  rw [← AlgHom.comp_apply, comp_aeval, fibreQ]
  refine congrArg (fun x => aeval x (gMixed k)) ?_
  funext r
  simp [map_sum, mapAlgHom_apply, map_X, map_C]
  rfl

theorem continuous_coeff (k : ℕ) (μ : Fin 3 →₀ ℕ) : Continuous (coeff μ (fibreQ k)) := by
  rw [fibreQ_eq_map, mapAlgHom_apply, coeff_map]
  exact (coeff μ (aeval (fun r : Fin 2 => ∑ i : Fin 3, X i * C (coordC r i)) (gMixed k))).continuous

theorem integrable_term
    (hint : Integrable (fun p : Sphere2 × Sphere2 => kernelL ⟪(p.1 : E3), (p.2 : E3)⟫_ℝ)
      pairMeasure) (f : Sphere2 × Sphere2 → ℝ) (hf : Continuous f) :
    Integrable (fun p => kernelL ⟪(p.1 : E3), (p.2 : E3)⟫_ℝ * f p) pairMeasure := by
  let f' : C(Sphere2 × Sphere2, ℝ) := ⟨f, hf⟩
  exact hint.mul_bdd (c := ‖f'‖) hf.aestronglyMeasurable
    (Filter.Eventually.of_forall fun p => f'.norm_coe_le_norm p)

theorem integrable_kernel (h0 : FibreConstantClosedForm.Statement) :
    Integrable (fun p : Sphere2 × Sphere2 => kernelL ⟪(p.1 : E3), (p.2 : E3)⟫_ℝ) pairMeasure := by
  have h1 : fibreConstant 1 ≠ 0 := by
    intro h
    have := h0.2.1
    rw [h] at this
    norm_num at this
  by_contra hni
  apply h1
  rw [fibreConstant, gMixed_one]
  simp only [map_one, mul_one]
  exact integral_undef hni

theorem eval_fibreQ (k : ℕ) (a : Fin 3 → ℝ) (p : Sphere2 × Sphere2) :
    eval₂ (Pi.evalRingHom (fun _ : Sphere2 × Sphere2 => ℝ) p) a (fibreQ k) =
      eval ![⟪WithLp.toLp 2 a, (p.1 : E3)⟫_ℝ, ⟪WithLp.toLp 2 a, (p.2 : E3)⟫_ℝ] (gMixed k) := by
  rw [fibreQ, ← coe_eval₂Hom, map_aeval]
  have hc : (eval₂Hom (Pi.evalRingHom (fun _ : Sphere2 × Sphere2 => ℝ) p) a).comp
      (algebraMap ℝ _) = RingHom.id ℝ := by
    ext c
    simp
  rw [hc]
  change eval _ (gMixed k) = eval _ (gMixed k)
  refine congrArg (fun v => eval v (gMixed k)) ?_
  funext r
  fin_cases r <;> simp [PiLp.inner_apply, mul_comm]

theorem fibrePoly_eq_C (h0 : FibreConstantClosedForm.Statement) (k : ℕ) :
    fibrePoly k = C (fibreConstant k) * (∑ i, X i ^ 2) ^ (k - 1) := by
  have hint := integrable_kernel h0
  apply MvPolynomial.funext
  intro a
  have hmean := mean_eq k (WithLp.toLp 2 a)
  have haa : ⟪(WithLp.toLp 2 a : E3), WithLp.toLp 2 a⟫_ℝ = ∑ i, a i ^ 2 := by
    rw [real_inner_self_eq_norm_sq, EuclideanSpace.norm_sq_eq]
    simp [sq_abs]
  rw [haa] at hmean
  simp only [map_mul, map_pow, map_sum, eval_C, eval_X]
  rw [← hmean, fibrePoly_eq, map_sum]
  simp only [eval_monomial]
  simp_rw [← integral_mul_const]
  rw [← integral_finsetSum _
    (fun μ _ => (integrable_term hint _ (continuous_coeff k μ)).mul_const _)]
  congr 1
  funext p
  rw [← eval_fibreQ, eval₂_eq, Finset.mul_sum]
  refine Finset.sum_congr rfl fun μ _ => ?_
  simp [Finsupp.prod]
  ring

theorem proof (h0 : FibreConstantClosedForm.Statement) : FibreIntegralInvariant.Statement := by
  refine ⟨mean_eq, fun k B _ _ a => ?_⟩
  rw [fibrePoly_eq_C h0 k]
  simp [map_mul, map_pow, map_sum, aeval_X]

end FibreIntegralInvariant

end

end GroundTheory.Heights₂.Heights.FlagBundles
