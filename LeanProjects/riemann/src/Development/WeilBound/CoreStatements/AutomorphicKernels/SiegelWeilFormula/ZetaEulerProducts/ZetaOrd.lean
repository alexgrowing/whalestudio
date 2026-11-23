import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.ZetaEulerProducts.InvGammaRZo
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.ZetaEulerProducts.SummablePrimesRpow

open Filter Topology Complex NumberField InfinitePlace
open scoped Real

namespace PositivityTheory.Lord

open GroundTheory.Global

theorem zeta_analyticAt (K : Type) [Field K] [NumberField K] {x : ℂ} (hx : x ≠ 1) :
    AnalyticAt ℂ (continuedDedekindZeta K) x :=
  (differentiableOn_continuedDedekindZeta K).analyticAt (isOpen_compl_singleton.mem_nhds hx)

theorem zeta_pole (K : Type) [Field K] [NumberField K] :
    ∃ A : ℂ → ℂ, AnalyticAt ℂ A 1 ∧ A 1 ≠ 0 ∧
      ∀ᶠ s in 𝓝[≠] (1 : ℂ), (s - 1) * continuedDedekindZeta K s = A s := by
  refine ⟨Function.update (fun s => (s - 1) * continuedDedekindZeta K s) 1 (dedekindZeta_residue K : ℂ),
    (differentiable_sub_one_mul_continuedDedekindZeta K).analyticAt 1, ?_, ?_⟩
  · rw [Function.update_apply, if_pos rfl]
    exact Complex.ofReal_ne_zero.mpr (dedekindZeta_residue_ne_zero K)
  · filter_upwards [self_mem_nhdsWithin] with s hs
    rw [Function.update_apply, if_neg (show s ≠ 1 from hs)]

theorem completed_zeta_continued_eq (K : Type) [Field K] [NumberField K] {s : ℂ} (hs0 : s ≠ 0) :
    continuedDedekindZeta K s = ((|(discr K : ℝ)| : ℝ) : ℂ) ^ (-(s / 2)) *
      ((Gammaℝ s)⁻¹ ^ nrRealPlaces K * (Gammaℂ s)⁻¹ ^ nrComplexPlaces K) * completedDedekindZeta K s := by
  rw [continuedDedekindZeta_of_ne_zero K hs0, normalizedDedekindZeta, mul_inv, inv_pow, inv_pow]

theorem discr_cpow_analytic (K : Type) [Field K] [NumberField K] (x : ℂ) :
    AnalyticAt ℂ (fun s : ℂ => ((|(discr K : ℝ)| : ℝ) : ℂ) ^ (-(s / 2))) x ∧
      ((|(discr K : ℝ)| : ℝ) : ℂ) ^ (-(x / 2)) ≠ 0 := by
  have hpos : (0 : ℝ) < |(discr K : ℝ)| := abs_pos.mpr (Int.cast_ne_zero.mpr (discr_ne_zero K))
  refine ⟨AnalyticAt.cpow analyticAt_const (by fun_prop) (Complex.ofReal_mem_slitPlane.mpr hpos), ?_⟩
  rw [Ne, Complex.cpow_eq_zero_iff]
  exact fun h => (Complex.ofReal_ne_zero.mpr hpos.ne') h.1

theorem gammaInv_zo (K : Type) [Field K] [NumberField K] (j : ℤ) (hj : j ≤ 0) :
    ZO (fun s => (Gammaℝ s)⁻¹ ^ nrRealPlaces K * (Gammaℂ s)⁻¹ ^ nrComplexPlaces K) (j : ℂ)
      ((if Even j then 1 else 0) * nrRealPlaces K + 1 * nrComplexPlaces K) :=
  ((invGammaR_zo j hj).pow _).mul ((invGammaC_zo j hj).pow _)

theorem one_le_places (K : Type) [Field K] [NumberField K] : 1 ≤ nrRealPlaces K + nrComplexPlaces K := by
  have h := card_add_two_mul_card_eq_rank K
  have h1 : 0 < Module.finrank ℚ K := Module.finrank_pos
  omega

theorem zeta_zo_nonpos (K : Type) [Field K] [NumberField K] (j : ℤ) (hj : j ≤ 0) :
    ZO (continuedDedekindZeta K) (j : ℂ)
      (nrRealPlaces K * (if Even j then 1 else 0) + nrComplexPlaces K - (if j = 0 then 1 else 0)) := by
  have hG := gammaInv_zo K j hj
  rcases hj.lt_or_eq with hlt | rfl
  · have hb := discr_cpow_analytic K (j : ℂ)
    have hne : j ≠ 0 := hlt.ne
    have hj0 : (j : ℂ) ≠ 0 := by exact_mod_cast hne
    have hj1 : (j : ℂ) ≠ 1 := by
      intro h
      have : j = 1 := by exact_mod_cast h
      omega
    have hΛa : AnalyticAt ℂ (completedDedekindZeta K) (j : ℂ) := by
      refine DifferentiableOn.analyticAt (s := {0}ᶜ ∩ {1}ᶜ) (fun z hz => ?_)
        ((isOpen_compl_singleton.inter isOpen_compl_singleton).mem_nhds ⟨hj0, hj1⟩)
      exact (differentiableAt_completedDedekindZeta K hz.1 hz.2).differentiableWithinAt
    have hΛ0 : completedDedekindZeta K (j : ℂ) ≠ 0 := by
      intro h0
      have hre : 1 < (1 - (j : ℂ)).re := by
        have : (j : ℝ) < 0 := by exact_mod_cast hlt
        simp only [Complex.sub_re, Complex.one_re, Complex.intCast_re]
        linarith
      have hs1 : (1 - (j : ℂ)) ≠ 0 := by
        intro h
        rw [h, Complex.zero_re] at hre
        exact absurd hre (by norm_num)
      have e1 := completedDedekindZeta_one_sub K hj0 hj1
      have e2 := completed_zeta_continued_eq K hs1
      rw [e1, h0, mul_zero] at e2
      exact (zeta_euler K hre).2 e2
    have Z := ((ZO.of_analytic hb.1 hb.2).mul hG).mul (ZO.of_analytic hΛa hΛ0)
    have hord : nrRealPlaces K * (if Even j then 1 else 0) + nrComplexPlaces K - (if j = 0 then 1 else 0)
        = 0 + ((if Even j then 1 else 0) * nrRealPlaces K + 1 * nrComplexPlaces K) + 0 := by
      rw [if_neg hne, Nat.sub_zero]
      ring
    rw [hord]
    refine Z.congr ?_
    filter_upwards [nhdsWithin_le_nhds (isOpen_compl_singleton.mem_nhds hj0)] with s hs
    exact (completed_zeta_continued_eq K hs).symm
  · have he : Even (0 : ℤ) := ⟨0, rfl⟩
    simp only [Int.cast_zero, he, ↓reduceIte, one_mul, mul_one] at hG ⊢
    have hm : 1 ≤ nrRealPlaces K + nrComplexPlaces K := one_le_places K
    obtain ⟨k, hk⟩ : ∃ k, nrRealPlaces K + nrComplexPlaces K = k + 1 :=
      ⟨_, (Nat.sub_add_cancel hm).symm⟩
    rw [hk] at hG
    rw [hk, Nat.add_sub_cancel]
    have hb0 := discr_cpow_analytic K 0
    obtain ⟨L, hT, hL0⟩ : ∃ L : ℂ, Tendsto (fun s => s * completedDedekindZeta K s) (𝓝[≠] 0) (𝓝 L) ∧ L ≠ 0 := by
      refine ⟨_, tendsto_mul_completedDedekindZeta_zero K, ?_⟩
      have h1 : (0 : ℝ) < √|(discr K : ℝ)| * dedekindZeta_residue K :=
        mul_pos (Real.sqrt_pos.mpr (abs_pos.mpr (Int.cast_ne_zero.mpr (discr_ne_zero K))))
          (dedekindZeta_residue_pos K)
      exact neg_ne_zero.mpr (mul_ne_zero (Complex.ofReal_ne_zero.mpr h1.ne')
        (inv_ne_zero (pow_ne_zero _ (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))))
    set F : ℂ → ℂ := Function.update (fun s => s * completedDedekindZeta K s) 0 L with hFdef
    have hFa : AnalyticAt ℂ F 0 := by
      apply Complex.analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt
      · filter_upwards [self_mem_nhdsWithin,
          nhdsWithin_le_nhds (isOpen_compl_singleton.mem_nhds (zero_ne_one : (0 : ℂ) ≠ 1))] with z hz0 hz1
        have hd : DifferentiableAt ℂ (fun s => s * completedDedekindZeta K s) z :=
          differentiableAt_id.mul (differentiableAt_completedDedekindZeta K hz0 hz1)
        refine hd.congr_of_eventuallyEq ?_
        filter_upwards [isOpen_compl_singleton.mem_nhds hz0] with w hw
        rw [hFdef, Function.update_apply, if_neg (show w ≠ 0 from hw)]
      · rw [hFdef]
        exact continuousAt_update_same.mpr hT
    unfold ZO at hG ⊢
    obtain ⟨u, hu, hu0, hGu⟩ := hG
    refine ⟨fun s => ((|(discr K : ℝ)| : ℝ) : ℂ) ^ (-(s / 2)) * u s * F s, (hb0.1.mul hu).mul hFa, ?_, ?_⟩
    · refine mul_ne_zero (mul_ne_zero hb0.2 hu0) ?_
      rw [hFdef, Function.update_apply, if_pos rfl]
      exact hL0
    · filter_upwards [self_mem_nhdsWithin, hGu] with s hs hGs
      beta_reduce at hGs
      rw [completed_zeta_continued_eq K hs, hGs]
      have hFs : F s = s * completedDedekindZeta K s := by
        rw [hFdef, Function.update_apply, if_neg (show s ≠ 0 from hs)]
      rw [hFs, pow_succ]
      ring

end PositivityTheory.Lord
