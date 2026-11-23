import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.IsDCReps
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.WirtingerEichlerStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GreenFormulaPeriodicRectangleUpperHalfPlaneStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IntegralConjMulExpEqConjQExpansionCoeffStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CoeffEqZeroOfExpDecayOfIntegralIdentityStatement
open GlobalTheory.HeckeFamilyMatrices Polynomial UpperHalfPlane
open scoped MatrixGroups ModularForm
open scoped Manifold

namespace GlobalTheory.EichlerPositivity

theorem periodic_of_dbar : ∀ (U : ℂ → ℂ) (h : ℍ → ℂ) (w : ℕ) (T : ℝ), (∀ s : ℂ, 0 < s.im → ∃ L : ℂ →L[ℝ] ℂ, HasFDerivAt U L s ∧ L Complex.I - Complex.I * L 1 = 2 * Complex.I * (s - (starRingEnd ℂ) s) ^ w * (starRingEnd ℂ) (h (ofComplex s))) → (∀ s : ℂ, 0 < s.im → U (s + T) = U s) → ∀ s : ℂ, 0 < s.im → h (ofComplex (s + T)) = h (ofComplex s) := by
  intro U h w T hd hp s hs
  have hsT : 0 < (s + T).im := by simpa using hs
  obtain ⟨L0, hL0, e0⟩ := hd s hs
  obtain ⟨L1, hL1, e1⟩ := hd (s + T) hsT
  have hshift : HasFDerivAt (fun z : ℂ => U (z + T)) L1 s := by
    have := hL1.comp s ((hasFDerivAt_id (𝕜 := ℝ) s).add_const (T : ℂ))
    simpa [Function.comp_def] using this
  have hev : U =ᶠ[nhds s] fun z : ℂ => U (z + T) :=
    ((Complex.continuous_im.tendsto s).eventually (lt_mem_nhds hs)).mono fun z hz => (hp z hz).symm
  have hL : L0 = L1 := hL0.unique (hshift.congr_of_eventuallyEq hev)
  have hconj : (s + T) - (starRingEnd ℂ) (s + T) = s - (starRingEnd ℂ) s := by
    simp only [map_add, Complex.conj_ofReal]; ring
  have hne : 2 * Complex.I * (s - (starRingEnd ℂ) s) ^ w ≠ 0 := by
    have : s - (starRingEnd ℂ) s ≠ 0 := by
      rw [Complex.sub_conj]
      exact mul_ne_zero (by exact_mod_cast (by positivity : (2 * s.im) ≠ 0)) Complex.I_ne_zero
    exact mul_ne_zero (mul_ne_zero two_ne_zero Complex.I_ne_zero) (pow_ne_zero _ this)
  have key := e1
  rw [hconj, ← hL, e0] at key
  exact ((starRingEnd ℂ).injective (mul_left_cancel₀ hne key)).symm

theorem fourier_sub_eq : ∀ (U : ℂ → ℂ) (h : ℍ → ℂ) (w : ℕ) (T : ℝ) (n : ℕ) (a b : ℝ), 0 < T → 0 < a → a ≤ b → (∀ s : ℂ, 0 < s.im → ∃ L : ℂ →L[ℝ] ℂ, HasFDerivAt U L s ∧ L Complex.I - Complex.I * L 1 = 2 * Complex.I * (s - (starRingEnd ℂ) s) ^ w * (starRingEnd ℂ) (h (ofComplex s))) → (∀ s : ℂ, 0 < s.im → U (s + T) = U s) → MDifferentiable 𝓘(ℂ) 𝓘(ℂ) h → Function.Periodic (h ∘ ofComplex) T → IsBoundedAtImInfty h → (∫ x in (0 : ℝ)..T, U ((x : ℂ) + (b : ℂ) * Complex.I) * Complex.exp (2 * Real.pi * Complex.I * n * ((x : ℂ) + (b : ℂ) * Complex.I) / T)) - (∫ x in (0 : ℝ)..T, U ((x : ℂ) + (a : ℂ) * Complex.I) * Complex.exp (2 * Real.pi * Complex.I * n * ((x : ℂ) + (a : ℂ) * Complex.I) / T)) = 2 * Complex.I * (2 * Complex.I) ^ w * T * (starRingEnd ℂ) ((qExpansion T h).coeff n) * ∫ y in a..b, (y : ℂ) ^ w * (Real.exp (-(4 * Real.pi * n / T) * y) : ℂ) := by
  intro U h w T n a b hT ha hab hd hp hh hper hbdd
  have hT' : (T : ℂ) ≠ 0 := by exact_mod_cast hT.ne'
  refine (GlobalTheory.T.green_formula_periodic_rectangle_upperHalfPlane (fun z => U z * Complex.exp (2 * Real.pi * Complex.I * n * z / T))
    (fun s => Complex.exp (2 * Real.pi * Complex.I * n * s / T) *
      (2 * Complex.I * (s - (starRingEnd ℂ) s) ^ w * (starRingEnd ℂ) (h (ofComplex s))))
    T a b hT ha hab ?_ ?_ ?_).trans ?_
  · intro s hs
    obtain ⟨L, hL, e⟩ := hd s hs
    have h1 : HasDerivAt (fun z : ℂ => 2 * Real.pi * Complex.I * n * z / T)
        (2 * Real.pi * Complex.I * n / T) s := by
      simpa using ((hasDerivAt_id s).const_mul (2 * Real.pi * Complex.I * n : ℂ)).div_const (T : ℂ)
    refine ⟨_, hL.mul (h1.cexp.hasFDerivAt.restrictScalars ℝ), ?_⟩
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.coe_restrictScalars', ContinuousLinearMap.toSpanSingleton_apply, smul_eq_mul]
    linear_combination (Complex.exp (2 * Real.pi * Complex.I * n * s / T)) * e
  · have hc : ContinuousOn (h ∘ ofComplex) {s : ℂ | 0 < s.im} :=
      (UpperHalfPlane.mdifferentiable_iff.1 hh).continuousOn
    refine ContinuousOn.mul (Continuous.continuousOn (by fun_prop)) (ContinuousOn.mul
      (Continuous.continuousOn ?_) (Complex.continuous_conj.comp_continuousOn hc))
    exact continuous_const.mul ((continuous_id.sub Complex.continuous_conj).pow w)
  · intro s hs
    show U (s + T) * Complex.exp _ = U s * Complex.exp _
    rw [hp s hs]
    congr 1
    rw [show 2 * (Real.pi : ℂ) * Complex.I * n * (s + T) / T =
        2 * Real.pi * Complex.I * n * s / T + n * (2 * Real.pi * Complex.I) by field_simp,
      Complex.exp_add, Complex.exp_nat_mul_two_pi_mul_I, mul_one]
  · have inner : ∀ y ∈ Set.uIcc a b,
        (∫ x in (0 : ℝ)..T, Complex.exp (2 * Real.pi * Complex.I * n * ((x : ℂ) + (y : ℂ) * Complex.I) / T) *
          (2 * Complex.I * (((x : ℂ) + (y : ℂ) * Complex.I) - (starRingEnd ℂ) ((x : ℂ) + (y : ℂ) * Complex.I)) ^ w *
            (starRingEnd ℂ) (h (ofComplex ((x : ℂ) + (y : ℂ) * Complex.I))))) =
        2 * Complex.I * (2 * Complex.I) ^ w * T * (starRingEnd ℂ) ((qExpansion T h).coeff n) *
          ((y : ℂ) ^ w * (Real.exp (-(4 * Real.pi * n / T) * y) : ℂ)) := by
      intro y hy
      have hy0 : 0 < y := by
        rw [Set.uIcc_of_le hab] at hy
        exact lt_of_lt_of_le ha hy.1
      have hpt : ∀ x : ℝ, ((x : ℂ) + (y : ℂ) * Complex.I) - (starRingEnd ℂ) ((x : ℂ) + (y : ℂ) * Complex.I) =
          2 * Complex.I * y := by
        intro x
        rw [Complex.sub_conj]
        simp
        ring
      simp_rw [hpt]
      have hfun : (fun x : ℝ => Complex.exp (2 * Real.pi * Complex.I * n * ((x : ℂ) + (y : ℂ) * Complex.I) / T) *
          (2 * Complex.I * (2 * Complex.I * (y : ℂ)) ^ w *
            (starRingEnd ℂ) (h (ofComplex ((x : ℂ) + (y : ℂ) * Complex.I))))) =
          fun x : ℝ => (2 * Complex.I * (2 * Complex.I) ^ w * (y : ℂ) ^ w) *
            ((starRingEnd ℂ) (h (ofComplex ((x : ℂ) + (y : ℂ) * Complex.I))) *
              Complex.exp (2 * Real.pi * Complex.I * n * ((x : ℂ) + (y : ℂ) * Complex.I) / T)) := by
        funext x
        rw [mul_pow]
        ring
      rw [hfun, intervalIntegral.integral_const_mul, GlobalTheory.T.integral_conj_mul_exp_eq_conj_qExpansion_coeff h T n y hT hy0 hh hper hbdd]
      ring
    rw [intervalIntegral.integral_congr inner, intervalIntegral.integral_const_mul]

theorem cuspForm_eq_zero_of_periodic_of_bound : ∀ (Γ : Subgroup SL(2, ℤ)) (k : ℕ), Γ.FiniteIndex → 3 ≤ k → ∀ (f h : CuspForm Γ (k : ℤ)) (p : ℂ[X]) (h₀ : ℕ) (C : ℝ), 0 < h₀ → (∀ τ : ℍ, (eichler (k - 2) ⇑f ((h₀ : ℝ) +ᵥ τ) - (eichler (k - 2) ⇑h ((h₀ : ℝ) +ᵥ τ)).map (starRingEnd ℂ) - p).eval (((h₀ : ℝ) +ᵥ τ : ℍ) : ℂ) = (eichler (k - 2) ⇑f τ - (eichler (k - 2) ⇑h τ).map (starRingEnd ℂ) - p).eval (τ : ℂ)) → (∀ τ : ℍ, ‖(eichler (k - 2) ⇑f τ - (eichler (k - 2) ⇑h τ).map (starRingEnd ℂ) - p).eval (τ : ℂ)‖ ≤ C * τ.im ^ (((k : ℝ) - 2) / 2)) → h = 0 := by
  intro Γ k hfi hk f h p h₀ C hh₀ hper hbd
  have := hfi
  have hT : (0 : ℝ) < (h₀ : ℝ) := by exact_mod_cast hh₀
  have hcoe : ∀ z : ℂ, 0 < z.im → ((ofComplex z : ℍ) : ℂ) = z := fun z hz => by
    rw [ofComplex_apply_of_im_pos hz]
  have hholo : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (⇑h) := ModularFormClass.holo h
  have hd := GlobalTheory.T.hasFDerivAt_eichler_sub_conj_wirtinger (k - 2) ⇑f ⇑h p (ModularFormClass.holo f) hholo
  have hUper : ∀ s : ℂ, 0 < s.im →
      (eichler (k - 2) ⇑f (ofComplex (s + ((h₀ : ℝ) : ℂ))) -
          (eichler (k - 2) ⇑h (ofComplex (s + ((h₀ : ℝ) : ℂ)))).map (starRingEnd ℂ) - p).eval
          (s + ((h₀ : ℝ) : ℂ)) =
        (eichler (k - 2) ⇑f (ofComplex s) - (eichler (k - 2) ⇑h (ofComplex s)).map (starRingEnd ℂ) - p).eval s := by
    intro s hs
    have hs' : 0 < (s + ((h₀ : ℝ) : ℂ)).im := by simpa using hs
    have e : ofComplex (s + ((h₀ : ℝ) : ℂ)) = ((h₀ : ℝ) +ᵥ ofComplex s) := by
      ext
      rw [UpperHalfPlane.coe_vadd, hcoe _ hs', hcoe _ hs]
      ring
    have key := hper (ofComplex s)
    rw [← e, hcoe _ hs', hcoe _ hs] at key
    exact key
  have hhper := periodic_of_dbar _ ⇑h (k - 2) (h₀ : ℝ) hd hUper
  have hperh : Function.Periodic (⇑h ∘ ofComplex) ((h₀ : ℝ) : ℂ) := by
    intro s
    by_cases hs : 0 < s.im
    · exact hhper s hs
    · rw [not_lt] at hs
      simp only [Function.comp_apply]
      rw [ofComplex_apply_eq_of_im_nonpos (by simpa using hs) hs]
  have hbdd : IsBoundedAtImInfty (⇑h) := ModularFormClass.bdd_at_infty h
  have hzero : IsZeroAtImInfty (⇑h) := CuspFormClass.zero_at_infty h
  have hq : qExpansion (h₀ : ℝ) ⇑h = 0 := by
    refine PowerSeries.ext fun n => ?_
    rw [map_zero]
    rcases n with _ | n
    · rw [qExpansion_coeff_zero hT (analyticAt_cuspFunction_zero hT hperh hholo hbdd) hperh,
        hzero.valueAtInfty_eq_zero]
    · have hm : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
      have hα : 0 < 2 * Real.pi * ((n + 1 : ℕ) : ℝ) / (h₀ : ℝ) := by positivity
      have hβ : 0 < 4 * Real.pi * ((n + 1 : ℕ) : ℝ) / (h₀ : ℝ) := by positivity
      have hK : 2 * Complex.I * (2 * Complex.I) ^ (k - 2) * ((h₀ : ℝ) : ℂ) ≠ 0 := by
        have : ((h₀ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hT.ne'
        exact mul_ne_zero (mul_ne_zero (mul_ne_zero two_ne_zero Complex.I_ne_zero)
          (pow_ne_zero _ (mul_ne_zero two_ne_zero Complex.I_ne_zero))) this
      have hw1 : 1 ≤ k - 2 := by omega
      have hwR : (((k - 2 : ℕ) : ℝ)) = (k : ℝ) - 2 := by
        rw [Nat.cast_sub (by omega)]
        norm_num
      have hbound : ∀ y : ℝ, 0 < y →
          ‖∫ x in (0 : ℝ)..(h₀ : ℝ),
              (eichler (k - 2) ⇑f (ofComplex ((x : ℂ) + (y : ℂ) * Complex.I)) -
                (eichler (k - 2) ⇑h (ofComplex ((x : ℂ) + (y : ℂ) * Complex.I))).map (starRingEnd ℂ) - p).eval
                ((x : ℂ) + (y : ℂ) * Complex.I) *
              Complex.exp (2 * Real.pi * Complex.I * ((n + 1 : ℕ) : ℂ) * ((x : ℂ) + (y : ℂ) * Complex.I) / ((h₀ : ℝ) : ℂ))‖ ≤
            (C * (h₀ : ℝ)) * y ^ ((((k - 2 : ℕ) : ℝ)) / 2) *
              Real.exp (-(2 * Real.pi * ((n + 1 : ℕ) : ℝ) / (h₀ : ℝ)) * y) := by
        intro y hy
        have hpt : ∀ x : ℝ,
            ‖(eichler (k - 2) ⇑f (ofComplex ((x : ℂ) + (y : ℂ) * Complex.I)) -
                (eichler (k - 2) ⇑h (ofComplex ((x : ℂ) + (y : ℂ) * Complex.I))).map (starRingEnd ℂ) - p).eval
                ((x : ℂ) + (y : ℂ) * Complex.I) *
              Complex.exp (2 * Real.pi * Complex.I * ((n + 1 : ℕ) : ℂ) * ((x : ℂ) + (y : ℂ) * Complex.I) / ((h₀ : ℝ) : ℂ))‖ ≤
            C * y ^ ((((k - 2 : ℕ) : ℝ)) / 2) * Real.exp (-(2 * Real.pi * ((n + 1 : ℕ) : ℝ) / (h₀ : ℝ)) * y) := by
          intro x
          have hz : 0 < ((x : ℂ) + (y : ℂ) * Complex.I).im := by simpa using hy
          have hb := hbd (ofComplex ((x : ℂ) + (y : ℂ) * Complex.I))
          rw [hcoe _ hz] at hb
          have him : (ofComplex ((x : ℂ) + (y : ℂ) * Complex.I)).im = y := by
            rw [← UpperHalfPlane.coe_im, hcoe _ hz]
            simp
          rw [him, ← hwR] at hb
          rw [norm_mul, Complex.norm_exp]
          have hre : (2 * Real.pi * Complex.I * ((n + 1 : ℕ) : ℂ) * ((x : ℂ) + (y : ℂ) * Complex.I) /
              ((h₀ : ℝ) : ℂ)).re = -(2 * Real.pi * ((n + 1 : ℕ) : ℝ) / (h₀ : ℝ)) * y := by
            rw [Complex.div_ofReal_re]
            simp
            ring
          rw [hre]
          exact mul_le_mul_of_nonneg_right hb (Real.exp_pos _).le
        have := intervalIntegral.norm_integral_le_of_norm_le_const (a := (0 : ℝ)) (b := (h₀ : ℝ))
          (fun x _ => hpt x)
        rw [sub_zero, abs_of_pos hT] at this
        calc _ ≤ _ := this
          _ = _ := by ring
      have hc := GlobalTheory.T.coeff_eq_zero_of_exp_decay_of_integral_identity _ (2 * Complex.I * (2 * Complex.I) ^ (k - 2) * ((h₀ : ℝ) : ℂ))
        ((starRingEnd ℂ) ((qExpansion (h₀ : ℝ) ⇑h).coeff (n + 1)))
        (C * (h₀ : ℝ)) _ (4 * Real.pi * ((n + 1 : ℕ) : ℝ) / (h₀ : ℝ)) (k - 2) hw1 hα hβ hK hbound
        (fun a b ha hab => fourier_sub_eq _ ⇑h (k - 2) (h₀ : ℝ) (n + 1) a b hT ha hab hd hUper
          hholo hperh hbdd)
      simpa using hc
  have hfun : (⇑h : ℍ → ℂ) = 0 := (qExpansion_eq_zero_iff hT hperh hholo hbdd).1 hq
  ext τ
  simpa using congrFun hfun τ

end GlobalTheory.EichlerPositivity
