import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.KappaA
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.KappaB
import GroundTheory.HeightsAndTheta.Heights.FlagBundles.Assembly
import GroundTheory.HeightsAndTheta.Heights.Intersections.StatementsFibreLocal
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Inter

open MeasureTheory MvPolynomial ReciprocityTheory.ChartRestriction.G.AI

noncomputable section

namespace FibreLocal

@[local instance] theorem isProbabilityMeasure_sphere : IsProbabilityMeasure sphereMeasure :=
  sphereInv_thm.1

theorem add_mul_gPoly (k : ℕ) :
    (X 0 + X 1 : MvPolynomial (Fin 2) ℝ) * gPoly k = X 1 * (X 0 ^ (2 * k) - X 1 ^ (2 * k)) := by
  have h := (Commute.all (-(X 1 : MvPolynomial (Fin 2) ℝ)) (X 0)).geom_sum₂_mul (2 * k)
  have hs : ∑ j ∈ Finset.range (2 * k),
      (-1 : ℝ) ^ j • ((X 0 : MvPolynomial (Fin 2) ℝ) ^ (2 * k - 1 - j) * X 1 ^ j) =
      ∑ i ∈ Finset.range (2 * k), (-(X 1 : MvPolynomial (Fin 2) ℝ)) ^ i * X 0 ^ (2 * k - 1 - i) := by
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Algebra.smul_def, map_pow, map_neg, map_one, neg_pow (X 1 : MvPolynomial (Fin 2) ℝ)]
    ring
  rw [gPoly, hs]
  rw [(even_two_mul k).neg_pow] at h
  linear_combination (-(X 1 : MvPolynomial (Fin 2) ℝ)) * h

theorem gPoly_eq (k : ℕ) : gPoly k = FlagBundles.gKernel ℝ k := by
  have hne : (X 0 + X 1 : MvPolynomial (Fin 2) ℝ) ≠ 0 := by
    intro h
    have := congrArg (eval ![1, 0]) h
    simp at this
  exact mul_left_cancel₀ hne (by rw [add_mul_gPoly, (FlagBundles.GKernelIdentity.full ℝ k).1])

theorem dgPoly_eq (k : ℕ) : dgPoly k = FlagBundles.gMixed k := by
  rw [dgPoly, FlagBundles.gMixed, gPoly_eq]

theorem integrable_kernel :
    Integrable (fun p : S2 × S2 => (1 / 2 : ℝ) * Real.log ((1 - inner ℝ (p.1 : E3) (p.2 : E3)) / 2))
      (sphereMeasure.prod sphereMeasure) :=
  FlagBundles.FibreIntegralInvariant.integrable_kernel FlagBundles.FibreConstantClosedForm.full

theorem integrable_mul (f : S2 × S2 → ℝ) (hf : Continuous f) :
    Integrable (fun p : S2 × S2 =>
      (1 / 2 : ℝ) * Real.log ((1 - inner ℝ (p.1 : E3) (p.2 : E3)) / 2) * f p)
      (sphereMeasure.prod sphereMeasure) :=
  FlagBundles.FibreIntegralInvariant.integrable_term integrable_kernel f hf

theorem continuous_evalPair (g : MvPolynomial (Fin 2) ℝ) (u v : S2 × S2 → ℝ) (hu : Continuous u)
    (hv : Continuous v) : Continuous fun p => eval ![u p, v p] g := by
  have h2 : Continuous fun p => (![u p, v p] : Fin 2 → ℝ) := by
    refine continuous_pi fun i => ?_
    fin_cases i
    · simpa using hu
    · simpa using hv
  exact (MvPolynomial.continuous_eval g).comp h2

theorem kappa_eq (k : ℕ) : kappa k = -FlagBundles.fibreConstant k := by
  have hc : Continuous fun p : S2 × S2 => eval ![(p.1 : E3) 2, (p.2 : E3) 2] (dgPoly k) :=
    continuous_evalPair _ _ _ ((EuclideanSpace.proj (2 : Fin 3)).continuous.comp
      (continuous_subtype_val.comp continuous_fst))
      ((EuclideanSpace.proj (2 : Fin 3)).continuous.comp (continuous_subtype_val.comp continuous_snd))
  rw [kappa, FlagBundles.fibreConstant, neg_inj]
  refine (integral_prod _ (integrable_mul _ hc)).symm.trans ?_
  simp_rw [dgPoly_eq]
  rfl

theorem sphere_moment (a : E3) (m : ℕ) :
    ∫ n : S2, inner ℝ a (n : E3) ^ (2 * m) ∂sphereMeasure = inner ℝ a a ^ m / (2 * m + 1) := by
  by_cases ha : a = 0
  · subst ha
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · simp
    · simp [inner_zero_left, zero_pow (by omega : 2 * m ≠ 0), zero_pow (by omega : m ≠ 0)]
  · set r : ℝ := ‖a‖ with hr
    have hr0 : r ≠ 0 := norm_ne_zero_iff.mpr ha
    set u : E3 := r⁻¹ • a with hu
    have hu1 : ‖u‖ = 1 := by rw [hu, norm_smul, norm_inv, norm_norm, ← hr, inv_mul_cancel₀ hr0]
    have hin : ∀ n : S2, inner ℝ a (n : E3) = r * inner ℝ (n : E3) u := by
      intro n
      rw [hu, inner_smul_right, real_inner_comm, ← mul_assoc, mul_inv_cancel₀ hr0, one_mul]
    have hA := (archimedes_thm u u u (fun t => (r * t) ^ (2 * m)) hu1
      (Continuous.intervalIntegrable (by fun_prop) _ _)).2.1
    simp_rw [hin]
    rw [hA]
    simp_rw [mul_pow]
    rw [intervalIntegral.integral_const_mul, integral_pow, real_inner_self_eq_norm_sq, ← hr]
    have h1 : ((-1 : ℝ)) ^ (2 * m + 1) = -1 := by rw [pow_succ, (even_two_mul m).neg_one_pow]; ring
    rw [h1, ← pow_mul]
    push_cast
    field_simp
    ring

theorem eval_momentPoly {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (w : Ω → ℝ)
    (Q : MvPolynomial (Fin 3) (Ω → ℝ)) (hQ : ∀ m, Integrable (fun p => w p * coeff m Q p) μ)
    (a : Fin 3 → ℝ) :
    eval a (momentPoly μ w Q) = ∫ p, w p * eval₂ (Pi.evalRingHom (fun _ : Ω => ℝ) p) a Q ∂μ := by
  rw [momentPoly, map_sum]
  simp only [eval_monomial]
  simp_rw [← integral_mul_const]
  rw [← integral_finsetSum _ (fun m _ => (hQ m).mul_const _)]
  congr 1
  funext p
  rw [eval₂_eq, Finset.mul_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  simp [Finsupp.prod]
  ring

def coordS (i : Fin 3) : C(S2, ℝ) :=
  ⟨fun n => (n : E3) i, (EuclideanSpace.proj i).continuous.comp continuous_subtype_val⟩

theorem dotPoly_id_pow (N : ℕ) :
    (dotPoly (id : S2 → S2)) ^ N =
      MvPolynomial.map (ContinuousMap.coeFnRingHom : C(S2, ℝ) →+* (S2 → ℝ)) ((∑ i, X i * C (coordS i)) ^ N) := by
  rw [map_pow, dotPoly]
  simp only [map_sum, map_mul, map_X, map_C]
  rfl

theorem pushMomentPoly_eq (k : ℕ) (hk : 1 ≤ k) :
    pushMomentPoly k = -(∑ i, X i ^ 2) ^ (k - 1) := by
  apply MvPolynomial.funext
  intro a
  have hQ : ∀ m, Integrable (fun p : S2 => (1 : ℝ) * coeff m ((dotPoly (id : S2 → S2)) ^ (2 * k - 2)) p)
      sphereMeasure := by
    intro m
    rw [dotPoly_id_pow, coeff_map]
    simp only [one_mul]
    exact (ContinuousMap.continuous (coeff m ((∑ i, X i * C (coordS i)) ^ (2 * k - 2)))).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  rw [pushMomentPoly, smul_eval, eval_momentPoly _ _ _ hQ]
  have he : ∀ p : S2, eval₂ (Pi.evalRingHom (fun _ : S2 => ℝ) p) a ((dotPoly id) ^ (2 * k - 2)) =
      inner ℝ (WithLp.toLp 2 a : E3) (p : E3) ^ (2 * k - 2) := by
    intro p
    rw [eval₂_pow, dotPoly]
    simp [eval₂_sum, PiLp.inner_apply, mul_comm]
  simp_rw [he, one_mul]
  have hkk : 2 * k - 2 = 2 * (k - 1) := by omega
  rw [hkk, sphere_moment]
  have haa : inner ℝ (WithLp.toLp 2 a : E3) (WithLp.toLp 2 a) = ∑ i, a i ^ 2 := by
    rw [real_inner_self_eq_norm_sq, EuclideanSpace.norm_sq_eq]
    simp [sq_abs]
  rw [haa]
  simp only [map_neg, map_pow, map_sum, eval_X]
  have hc : ((k - 1 : ℕ) : ℝ) = (k : ℝ) - 1 := by rw [Nat.cast_sub hk, Nat.cast_one]
  rw [hc]
  have hk' : (2 * ((k : ℝ) - 1) + 1) ≠ 0 := by
    have : (1 : ℝ) ≤ k := by exact_mod_cast hk
    linarith
  field_simp
  ring

theorem fibreMomentPoly_eq (k : ℕ) : fibreMomentPoly k = FlagBundles.fibrePoly k := by
  have hQ : aeval ![dotPoly (Prod.fst : S2 × S2 → S2), dotPoly Prod.snd] (dgPoly k) =
      FlagBundles.FibreIntegralInvariant.fibreQ k := by
    rw [FlagBundles.FibreIntegralInvariant.fibreQ, dgPoly_eq]
    refine congrArg (fun x => aeval x (FlagBundles.gMixed k)) ?_
    funext r
    fin_cases r <;> simp [dotPoly]
  rw [FlagBundles.FibreIntegralInvariant.fibrePoly_eq, fibreMomentPoly, momentPoly, hQ]
  rfl

theorem proof : FibreLocal.Statement := by
  refine ⟨fun k a => ?_, fun k B _ _ a => ?_, fun k hk a => ?_, fun k hk B _ _ a => ?_, fun k => ?_⟩
  · have hc : Continuous fun p : S2 × S2 => eval ![inner ℝ a (p.1 : E3), inner ℝ a (p.2 : E3)] (dgPoly k) :=
      continuous_evalPair _ _ _ (continuous_const.inner (continuous_subtype_val.comp continuous_fst))
        (continuous_const.inner (continuous_subtype_val.comp continuous_snd))
    refine (integral_prod _ (integrable_mul _ hc)).symm.trans ?_
    simp_rw [dgPoly_eq]
    rw [kappa_eq, neg_neg]
    exact FlagBundles.FibreIntegralInvariant.full.1 k a
  · rw [fibreMomentPoly_eq, FlagBundles.FibreIntegralInvariant.full.2 k B a, kappa_eq, neg_neg]
  · have hkk : 2 * k - 2 = 2 * (k - 1) := by omega
    rw [hkk, sphere_moment]
    have hc : ((k - 1 : ℕ) : ℝ) = (k : ℝ) - 1 := by rw [Nat.cast_sub hk, Nat.cast_one]
    rw [hc]
    have hk' : (2 * ((k : ℝ) - 1) + 1) ≠ 0 := by
      have : (1 : ℝ) ≤ k := by exact_mod_cast hk
      linarith
    field_simp
    ring
  · rw [pushMomentPoly_eq k hk]
    simp [map_neg, map_pow, map_sum, aeval_X]
  · rw [kappa_eq, FlagBundles.fibreConstant_eq]
    ring

end FibreLocal

end

end GroundTheory.Heights₂.Heights.Inter
