import Mathlib
import GroundTheory.AutomorphicForms.GL2.GJUnramified

open MeasureTheory Filter Set Topology Metric
open scoped ValuativeRel

namespace GroundTheory.Automorphic

noncomputable section

namespace GodementJacquet

open Matrix GLnLocal Parabolic Iwasawa Polynomial Spherical HeckeAlgebra

def homSum (m : ℕ) (b : Fin m → ℂ) (k : ℕ) : ℂ :=
  ∑ l ∈ Finset.Nat.antidiagonalTuple m k, ∏ i, b i ^ l i

theorem homSum_mul (m : ℕ) (b : Fin m → ℂ) (t : ℂ) (k : ℕ) :
    homSum m (fun i ↦ t * b i) k = t ^ k * homSum m b k := by
  unfold homSum
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun l hl ↦ ?_
  rw [← Finset.Nat.mem_antidiagonalTuple.1 hl]
  simp only [mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]

theorem norm_lt_one_of_summable {m : ℕ} {b : Fin m → ℂ} (h : Summable fun k ↦ ‖homSum m b k‖) (i : Fin m) :
    ‖b i‖ < 1 := by
  set P : ℂ → ℂ := fun t ↦ ∑' k, homSum m b k * t ^ k with hPdef
  set Q : ℂ → ℂ := fun t ↦ ∏ j, (1 - t * b j) with hQdef
  set R : ℂ → ℂ := fun t ↦ Q t * P t with hRdef
  have hterm : ∀ k, ∀ t ∈ closedBall (0 : ℂ) 1, ‖homSum m b k * t ^ k‖ ≤ ‖homSum m b k‖ := by
    intro k t ht
    rw [norm_mul, norm_pow]
    have ht1 : ‖t‖ ≤ 1 := by simpa using ht
    exact mul_le_of_le_one_right (norm_nonneg _) (pow_le_one₀ (norm_nonneg _) ht1)
  have hPd : DifferentiableOn ℂ P (ball 0 1) :=
    Complex.differentiableOn_tsum_of_summable_norm h
      (fun k ↦ ((differentiable_const _).mul (differentiable_pow k)).differentiableOn) isOpen_ball
      (fun k t ht ↦ hterm k t (ball_subset_closedBall ht))
  have hPc : ContinuousOn P (closedBall 0 1) :=
    continuousOn_tsum (fun k ↦ (continuous_const.mul (continuous_pow k)).continuousOn) h hterm
  have hQd : Differentiable ℂ Q := by
    rw [hQdef]
    fun_prop
  have hRa : AnalyticOnNhd ℂ R (ball 0 1) := (hQd.differentiableOn.mul hPd).analyticOnNhd isOpen_ball
  have hRc : ContinuousOn R (closedBall 0 1) := hQd.continuous.continuousOn.mul hPc

  set ε : ℝ := (1 + ∑ j, ‖b j‖)⁻¹ with hεdef
  have hpos : 0 < 1 + ∑ j, ‖b j‖ := by positivity
  have hε : 0 < ε := inv_pos.2 hpos
  have hnear : ∀ t : ℂ, ‖t‖ < ε → R t = 1 := by
    intro t ht
    have hsmall : ∀ j, ‖t * b j‖ < 1 := fun j ↦ by
      rw [norm_mul]
      have h2 : ‖b j‖ ≤ ∑ j, ‖b j‖ :=
        Finset.single_le_sum (f := fun j ↦ ‖b j‖) (fun j _ ↦ norm_nonneg _) (Finset.mem_univ j)
      calc ‖t‖ * ‖b j‖ ≤ ε * ∑ j, ‖b j‖ := mul_le_mul ht.le h2 (norm_nonneg _) hε.le
        _ < ε * (1 + ∑ j, ‖b j‖) := mul_lt_mul_of_pos_left (by linarith) hε
        _ = 1 := by rw [hεdef, inv_mul_cancel₀ hpos.ne']
    have hs := hasSum_sum_antidiagonalTuple hsmall
    have hP : P t = ∏ j, (1 - t * b j)⁻¹ := by
      rw [← hs.tsum_eq, hPdef]
      show ∑' k, homSum m b k * t ^ k = _
      congr 1
      funext k
      rw [← homSum, homSum_mul, mul_comm]
    have hne : ∀ j, 1 - t * b j ≠ 0 := fun j hj ↦ by
      have := hsmall j
      rw [← sub_eq_zero.1 hj, norm_one] at this
      exact lt_irrefl _ this
    simp only [hRdef, hQdef]
    rw [hP, ← Finset.prod_mul_distrib]
    exact Finset.prod_eq_one fun j _ ↦ mul_inv_cancel₀ (hne j)
  have hev : R =ᶠ[𝓝 0] fun _ ↦ (1 : ℂ) :=
    Filter.eventually_of_mem (ball_mem_nhds 0 hε) fun t ht ↦ hnear t (by simpa using ht)
  have hball : EqOn R (fun _ ↦ (1 : ℂ)) (ball 0 1) :=
    hRa.eqOn_of_preconnected_of_eventuallyEq analyticOnNhd_const (convex_ball 0 1).isPreconnected
      (mem_ball_self one_pos) hev
  have hclosed : EqOn R (fun _ ↦ (1 : ℂ)) (closedBall 0 1) :=
    hball.of_subset_closure hRc continuousOn_const ball_subset_closedBall
      (by rw [closure_ball (0 : ℂ) one_ne_zero])
  by_contra hi
  push Not at hi
  have hb0 : b i ≠ 0 := fun h0 ↦ by rw [h0, norm_zero] at hi; linarith
  have hmem : (b i)⁻¹ ∈ closedBall (0 : ℂ) 1 := by
    rw [mem_closedBall, dist_zero_right, norm_inv]
    exact inv_le_one_of_one_le₀ hi
  have h1 := hclosed hmem
  have h0 : Q (b i)⁻¹ = 0 :=
    Finset.prod_eq_zero (Finset.mem_univ i) (by rw [inv_mul_cancel₀ hb0, sub_self])
  simp only [hRdef, h0, zero_mul] at h1
  exact zero_ne_one h1

variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {n : ℕ} [MeasurableSpace (GL (Fin n) F)] [BorelSpace (GL (Fin n) F)]
  {V : Type*} [AddCommGroup V] [Module ℂ V] {π : Representation ℂ (GL (Fin n) F) V}

theorem zetaIntegral_sphericalCoeff_of_integrable (μ : Measure (GL (Fin n) F)) [μ.IsHaarMeasure]
    {z : Fin n → ℂˣ} (hz : IsSatakeParameter π μ z) {v₀ : V}
    (hv₀ : v₀ ∈ fixedVectors π (integralGL F n)) {ℓ₀ : Module.Dual ℂ V} (hℓ₀ : ℓ₀ v₀ = 1) {s : ℂ}
    (hI : Integrable (fun g : GL (Fin n) F ↦ integralIndicator F n (g : Matrix (Fin n) (Fin n) F) *
      matrixCoeff π v₀ ℓ₀ g * detPow g (s + ((n : ℂ) - 1) / 2)) μ) :
    (∀ i, ‖(z i : ℂ) * qs F s‖ < 1) ∧
      zetaIntegral μ (integralIndicator F n) (matrixCoeff π v₀ ℓ₀) s =
        (μ.real (integralGL F n : Set (GL (Fin n) F)) : ℂ) * ∏ i, (1 - (z i : ℂ) * qs F s)⁻¹ := by
  set H : GL (Fin n) F → ℂ := fun g : GL (Fin n) F ↦ integralIndicator F n (g : Matrix (Fin n) (Fin n) F) *
      matrixCoeff π v₀ ℓ₀ g * detPow g (s + ((n : ℂ) - 1) / 2) with hHdef
  set w : Fin n → ℂ := fun i ↦ (z i : ℂ) * qs F s with hwdef
  set c : ℂ := (μ.real (integralGL F n : Set (GL (Fin n) F)) : ℂ) with hcdef
  have hcpos : 0 < μ.real (integralGL F n : Set (GL (Fin n) F)) :=
    ENNReal.toReal_pos ((isOpen_integralGL F n).measure_pos μ ⟨1, (integralGL F n).one_mem⟩).ne'
      (isCompact_integralGL F n).measure_lt_top.ne
  have hterm : ∀ m : ℕ, ∫ g in {g : GL (Fin n) F | ordDet g = (m : ℤ)}, H g ∂μ = c * homSum n w m := by
    intro m
    rw [hHdef, integral_shell_integralIndicator, integral_mul_matrixCoeff_of_isSatakeParameter hz hv₀,
      hℓ₀, mul_one, evalAt_satakeTransform_integralHecke]
    have hprod : ∀ l ∈ Finset.Nat.antidiagonalTuple n m,
        ∏ i, ((z i : ℂ) * qs F s) ^ l i = qs F s ^ m * ∏ i, (z i : ℂ) ^ l i := by
      intro l hl
      rw [← Finset.Nat.mem_antidiagonalTuple.1 hl]
      simp only [mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
      ring
    rw [homSum, Finset.sum_congr rfl hprod, ← Finset.mul_sum, ← qs_shift_pow_mul_sqrtQ (n := n) s m]
    ring

  have hnorm : Summable fun m : ℕ ↦ ‖homSum n w m‖ := by
    have hIn : Integrable (fun g ↦ ((‖H g‖ : ℝ) : ℂ)) μ := hI.norm.ofReal
    have h1 := (hasSum_integral_shell μ hIn).summable
    have h2 : Summable fun k : ℤ ↦ ∫ g in {g : GL (Fin n) F | ordDet g = k}, ‖H g‖ ∂μ := by
      rw [← Complex.summable_ofReal]
      refine h1.congr fun k ↦ ?_
      exact integral_complex_ofReal
    have h3 := h2.comp_injective Nat.cast_injective
    refine Summable.of_nonneg_of_le (fun m ↦ norm_nonneg _) (fun m ↦ ?_)
      (h3.mul_left (μ.real (integralGL F n : Set (GL (Fin n) F)))⁻¹)
    have hle := norm_integral_le_integral_norm (μ := μ.restrict {g : GL (Fin n) F | ordDet g = (m : ℤ)}) H
    rw [hterm m, norm_mul, hcdef, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hcpos] at hle
    simp only [Function.comp_apply]
    rw [le_inv_mul_iff₀ hcpos]
    exact hle
  have hw := norm_lt_one_of_summable hnorm
  refine ⟨hw, ?_⟩
  have hsum := hasSum_integral_shell μ hI
  rw [← (Nat.cast_injective (R := ℤ)).hasSum_iff fun k hk ↦ by
    have hk' : k < 0 := by
      by_contra hc
      exact hk ⟨k.toNat, Int.toNat_of_nonneg (not_lt.1 hc)⟩
    exact integral_shell_integralIndicator_of_neg μ _ _ hk'] at hsum
  have hfun : ((fun k : ℤ ↦ ∫ g in {g : GL (Fin n) F | ordDet g = k},
      integralIndicator F n (g : Matrix (Fin n) (Fin n) F) * matrixCoeff π v₀ ℓ₀ g *
        detPow g (s + ((n : ℂ) - 1) / 2) ∂μ) ∘ Nat.cast) = fun m : ℕ ↦ c * homSum n w m :=
    funext hterm
  rw [hfun] at hsum
  rw [zetaIntegral]
  have hgen := (hasSum_sum_antidiagonalTuple hw).mul_left c
  exact hsum.unique hgen

end GodementJacquet

end

end GroundTheory.Automorphic
