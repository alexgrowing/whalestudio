import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaussSumFiltrations.EvenPos

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd GlobalTheory.HilbertThetaSeries
open scoped Matrix

noncomputable section

namespace GlobalTheory.HilbertThetaSeries.QHol

open UpperHalfPlane hiding I

variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F]

def lin (ξ : F) : (InfinitePlace F → ℂ) →L[ℂ] ℂ :=
  ∑ v, (reAt v ξ : ℂ) • ContinuousLinearMap.proj v

theorem lin_apply (ξ : F) (z : InfinitePlace F → ℂ) : lin ξ z = ∑ v, (reAt v ξ : ℂ) * z v := by
  simp [lin]

def sm (ξ : F) : ℝ := ∑ v, reAt v ξ

theorem norm_lin_le (ξ : F) (h : ∀ v, 0 ≤ reAt v ξ) : ‖lin ξ‖ ≤ sm ξ := by
  have hs : 0 ≤ sm ξ := Finset.sum_nonneg (fun v _ => h v)
  refine ContinuousLinearMap.opNorm_le_bound _ hs (fun z => ?_)
  rw [lin_apply]
  calc ‖∑ v, (reAt v ξ : ℂ) * z v‖ ≤ ∑ v, ‖(reAt v ξ : ℂ) * z v‖ := norm_sum_le _ _
    _ ≤ ∑ v, reAt v ξ * ‖z‖ := by
      apply Finset.sum_le_sum
      intro v _
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (h v)]
      exact mul_le_mul_of_nonneg_left (norm_le_pi_norm z v) (h v)
    _ = sm ξ * ‖z‖ := by rw [sm, Finset.sum_mul]

theorem re_lin (ξ : F) (z : InfinitePlace F → ℂ) :
    (2 * Real.pi * Complex.I * lin ξ z).re = -(2 * Real.pi * ∑ v, reAt v ξ * (z v).im) := by
  rw [lin_apply]
  simp [Complex.mul_re, Complex.mul_im, Complex.im_sum, Finset.mul_sum]

theorem ez_ofComplex (ξ : F) (z : InfinitePlace F → ℂ) (hz : ∀ v, 0 < (z v).im) :
    ez ξ (fun v => ofComplex (z v)) = Complex.exp (2 * Real.pi * Complex.I * lin ξ z) := by
  simp only [ez, lin_apply]
  congr 2
  apply Finset.sum_congr rfl
  intro v _
  rw [UpperHalfPlane.ofComplex_apply_of_im_pos (hz v)]

private theorem mul_exp_neg_le_exp_half (m x : ℝ) (hm : 0 < m) (hx : 0 ≤ x) :
    2 * Real.pi * x * Real.exp (-(2 * Real.pi * m * x)) ≤ (2 / m) * Real.exp (-(Real.pi * m * x)) := by
  set t := Real.pi * m * x with ht_def
  have ht : 0 ≤ t := by positivity
  have e : Real.exp (-(2 * Real.pi * m * x)) = Real.exp (-t) * Real.exp (-t) := by
    rw [← Real.exp_add]
    congr 1
    rw [ht_def]
    ring
  have hexp : Real.exp (-t) * Real.exp t = 1 := by
    rw [← Real.exp_add]
    simp
  have key : t * Real.exp (-t) ≤ 1 := by
    have := Real.add_one_le_exp t
    nlinarith [Real.exp_pos (-t)]
  have hx2 : 2 * Real.pi * x = (2 / m) * t := by
    rw [ht_def]
    field_simp
  rw [e, hx2]
  have hE : 0 ≤ (2 / m) * Real.exp (-t) := by positivity
  calc 2 / m * t * (Real.exp (-t) * Real.exp (-t)) = (2 / m) * Real.exp (-t) * (t * Real.exp (-t)) := by ring
    _ ≤ (2 / m) * Real.exp (-t) * 1 := mul_le_mul_of_nonneg_left key hE
    _ = (2 / m) * Real.exp (-t) := by ring

theorem hol : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (f : Hn F → ℂ) (a : F → ℂ),
    HasQ f a → Hol f := by
  intro F _ _ _ f a hQ
  obtain ⟨⟨D, hD, hsupp⟩, hsum⟩ := hQ
  have hpos : ∀ ξ, a ξ ≠ 0 → ∀ v, 0 ≤ reAt v ξ := by
    intro ξ hξ v
    rcases (hsupp ξ hξ).1 with h0 | htp
    · subst h0
      simp [reAt]
    · exact (htp v).le
  have hsm : ∀ ξ, a ξ ≠ 0 → 0 ≤ sm ξ := fun ξ hξ => Finset.sum_nonneg (fun v _ => hpos ξ hξ v)
  unfold Hol
  intro z0 hz0
  have hz0' : ∀ v, 0 < (z0 v).im := hz0
  obtain ⟨m, hmz, hm⟩ : ∃ m : ℝ, (∀ v, m < (z0 v).im) ∧ 0 < m := by
    have h1 : ∀ᶠ m in nhdsWithin (0 : ℝ) (Set.Ioi 0), ∀ v, m < (z0 v).im :=
      Filter.eventually_all.2 (fun v => eventually_nhdsWithin_of_eventually_nhds (eventually_lt_nhds (hz0' v)))
    exact (h1.and self_mem_nhdsWithin).exists
  set s : Set (InfinitePlace F → ℂ) := {z | ∀ v, m < (z v).im} with hs_def
  have hsopen : IsOpen s := by
    rw [hs_def, Set.setOf_forall]
    exact isOpen_iInter_of_finite (fun v => isOpen_lt continuous_const (Complex.continuous_im.comp (continuous_apply v)))
  have hsconv : Convex ℝ s := by
    intro x hx y hy p q hp hq hpq v
    have h1 := hx v
    have h2 := hy v
    simp only [Pi.add_apply, Pi.smul_apply, Complex.add_im, Complex.real_smul, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero]
    have e : p * (x v).im + q * (y v).im - m = p * ((x v).im - m) + q * ((y v).im - m) := by
      have : m = p * m + q * m := by rw [← add_mul, hpq, one_mul]
      linarith
    by_cases hp0 : p = 0
    · have hq1 : q = 1 := by linarith
      subst hp0 hq1
      linarith
    · have hp' : 0 < p := lt_of_le_of_ne hp (Ne.symm hp0)
      have := mul_pos hp' (sub_pos.2 h1)
      have := mul_nonneg hq (sub_pos.2 h2).le
      linarith
  have hz0s : z0 ∈ s := hmz
  have hpos_s : ∀ z ∈ s, ∀ v, 0 < (z v).im := fun z hz v => hm.trans (hz v)
  let g : F → (InfinitePlace F → ℂ) → ℂ := fun ξ z => a ξ * Complex.exp (2 * Real.pi * Complex.I * lin ξ z)
  let g' : F → (InfinitePlace F → ℂ) → ((InfinitePlace F → ℂ) →L[ℂ] ℂ) := fun ξ z =>
    a ξ • (Complex.exp (2 * Real.pi * Complex.I * lin ξ z) • ((2 * Real.pi * Complex.I) • lin ξ))
  let u : F → ℝ := fun ξ => ‖a ξ‖ * (2 * Real.pi * sm ξ * Real.exp (-(2 * Real.pi * m * sm ξ)))
  have hderiv : ∀ ξ z, z ∈ s → HasFDerivAt (g ξ) (g' ξ z) z := by
    intro ξ z _
    have h1 : HasFDerivAt (fun z => 2 * Real.pi * Complex.I * lin ξ z) ((2 * Real.pi * Complex.I) • lin ξ) z :=
      (lin ξ).hasFDerivAt.const_mul (2 * Real.pi * Complex.I)
    exact (h1.cexp).const_mul (a ξ)
  have hbound : ∀ ξ z, z ∈ s → ‖g' ξ z‖ ≤ u ξ := by
    intro ξ z hz
    by_cases ha : a ξ = 0
    · simp [g', u, ha]
    have hr := hpos ξ ha
    have hsum_le : m * sm ξ ≤ ∑ v, reAt v ξ * (z v).im := by
      rw [sm, Finset.mul_sum]
      apply Finset.sum_le_sum
      intro v _
      have := hz v
      nlinarith [hr v]
    simp only [g', u, norm_smul, Complex.norm_exp, re_lin]
    have hc : ‖(2 * (Real.pi : ℂ) * Complex.I)‖ = 2 * Real.pi := by
      simp [Real.pi_pos.le]
    rw [hc]
    have hL := norm_lin_le ξ hr
    have hexp : Real.exp (-(2 * Real.pi * ∑ v, reAt v ξ * (z v).im)) ≤ Real.exp (-(2 * Real.pi * m * sm ξ)) := by
      apply Real.exp_le_exp.2
      nlinarith [Real.pi_pos]
    have hn : 0 ≤ ‖a ξ‖ := norm_nonneg _
    calc ‖a ξ‖ * (Real.exp (-(2 * Real.pi * ∑ v, reAt v ξ * (z v).im)) * (2 * Real.pi * ‖lin ξ‖))
        ≤ ‖a ξ‖ * (Real.exp (-(2 * Real.pi * m * sm ξ)) * (2 * Real.pi * sm ξ)) := by
          apply mul_le_mul_of_nonneg_left _ hn
          apply mul_le_mul hexp _ (by positivity) (Real.exp_pos _).le
          exact mul_le_mul_of_nonneg_left hL (by positivity)
      _ = ‖a ξ‖ * (2 * Real.pi * sm ξ * Real.exp (-(2 * Real.pi * m * sm ξ))) := by ring
  let w : Hn F := fun _ => UpperHalfPlane.ofComplex (Complex.I * ((m / 2 : ℝ) : ℂ))
  have hw_im : ∀ v : InfinitePlace F, 0 < ((fun _ => Complex.I * ((m / 2 : ℝ) : ℂ)) v : ℂ).im := by
    intro v
    simp
    linarith
  have hnw : ∀ ξ, ‖a ξ * ez ξ w‖ = ‖a ξ‖ * Real.exp (-(Real.pi * m * sm ξ)) := by
    intro ξ
    have := ez_ofComplex ξ (fun _ => Complex.I * ((m / 2 : ℝ) : ℂ)) hw_im
    rw [norm_mul, this, Complex.norm_exp, re_lin]
    congr 2
    simp [sm, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro v _
    ring
  have hsw : Summable (fun ξ => ‖a ξ * ez ξ w‖) := (summable_norm_iff.2 (hsum w).summable)
  have hu : Summable u := by
    refine Summable.of_nonneg_of_le (fun ξ => ?_) (fun ξ => ?_) (hsw.mul_left (2 / m))
    · by_cases ha : a ξ = 0
      · simp [u, ha]
      · have := hsm ξ ha
        positivity
    · by_cases ha : a ξ = 0
      · simp [u, ha]
      · rw [hnw ξ]
        have := mul_exp_neg_le_exp_half m (sm ξ) hm (hsm ξ ha)
        calc u ξ = ‖a ξ‖ * (2 * Real.pi * sm ξ * Real.exp (-(2 * Real.pi * m * sm ξ))) := rfl
          _ ≤ ‖a ξ‖ * ((2 / m) * Real.exp (-(Real.pi * m * sm ξ))) := mul_le_mul_of_nonneg_left this (norm_nonneg _)
          _ = 2 / m * (‖a ξ‖ * Real.exp (-(Real.pi * m * sm ξ))) := by ring
  have hf0 : Summable (fun ξ => g ξ z0) := by
    refine (hsum (fun v => UpperHalfPlane.ofComplex (z0 v))).summable.congr (fun ξ => ?_)
    simp only [g]
    rw [ez_ofComplex ξ z0 hz0']
  have hT := hasFDerivAt_tsum_of_isPreconnected hu hsopen hsconv.isPreconnected hderiv hbound hz0s hf0 hz0s
  have heq : (fun z : InfinitePlace F → ℂ => f (fun v => UpperHalfPlane.ofComplex (z v))) =ᶠ[nhds z0]
      (fun y => ∑' ξ, g ξ y) := by
    filter_upwards [hsopen.mem_nhds hz0s] with y hy
    rw [← (hsum (fun v => UpperHalfPlane.ofComplex (y v))).tsum_eq]
    apply tsum_congr
    intro ξ
    simp only [g]
    rw [ez_ofComplex ξ y (hpos_s y hy)]
  exact (hT.differentiableAt.congr_of_eventuallyEq heq).differentiableWithinAt

end GlobalTheory.HilbertThetaSeries.QHol
