import Mathlib
import GroundTheory.GlobalFields.TateThesis.HeckeTheoremFE

open NumberField InfinitePlace IsDedekindDomain MeasureTheory Complex Topology Filter Set
open scoped NumberField.AdeleRing ComplexConjugate Real

namespace GroundTheory.Global

noncomputable section

variable {K : Type*} [Field K] [NumberField K]

open IdeleGroup

namespace HeckeCharacter

variable (χ : HeckeCharacter K)

theorem exists_normOne_ne_one_of_not
    (hχ : ¬ ∃ τ : ℝ, ∀ x : IdeleGroup K,
      (χ.toIdele x : ℂ) = ((ideleModule K x : ℝ) : ℂ) ^ ((τ : ℂ) * I)) :
    ∃ v : normOneSubgroup K, χ.toIdele (v : IdeleGroup K) ≠ 1 := by
  by_contra h
  push Not at h
  exact hχ ((forall_normOne_eq_one_iff χ).1 h)

theorem differentiable_completedLFunction
    (hχ : ¬ ∃ τ : ℝ, ∀ x : IdeleGroup K,
      (χ.toIdele x : ℂ) = ((ideleModule K x : ℝ) : ℂ) ^ ((τ : ℂ) * I)) :
    Differentiable ℂ χ.completedLFunction := fun s ↦
  χ.differentiable_const_mul_cpow_half
    (differentiable_tateZeta χ.testFunction_mem (χ.exists_normOne_ne_one_of_not hχ) s)

theorem LFunction_eq_mul_completedLFunction {s : ℂ} (hs : 1 < s.re) :
    χ.LFunction s = (χ.discrNormConductor : ℂ) ^ (-(s / 2)) * (χ.gammaFactor s)⁻¹ *
      χ.completedLFunction s := by
  have h1 := χ.discrNormConductor_cpow_ne_zero (s / 2)
  have h2 := χ.gammaFactor_ne_zero (by linarith : 0 < s.re)
  rw [χ.completedLFunction_eq hs, cpow_neg]
  field_simp

theorem differentiable_cpow_mul_gammaFactor_inv :
    Differentiable ℂ fun s ↦ (χ.discrNormConductor : ℂ) ^ (-(s / 2)) * (χ.gammaFactor s)⁻¹ :=
  ((differentiable_id.div_const 2).neg.const_cpow
    (Or.inl (ofReal_ne_zero.2 χ.discrNormConductor_pos.ne'))).mul χ.differentiable_gammaFactor_inv

theorem exists_LFunction_continuation
    (hχ : ¬ ∃ τ : ℝ, ∀ x : IdeleGroup K,
      (χ.toIdele x : ℂ) = ((ideleModule K x : ℝ) : ℂ) ^ ((τ : ℂ) * I)) :
    ∃ g : ℂ → ℂ, Differentiable ℂ g ∧ ∀ s : ℂ, 1 < s.re → g s = χ.LFunction s :=
  ⟨fun s ↦ (χ.discrNormConductor : ℂ) ^ (-(s / 2)) * (χ.gammaFactor s)⁻¹ * χ.completedLFunction s,
    χ.differentiable_cpow_mul_gammaFactor_inv.mul (χ.differentiable_completedLFunction hχ),
    fun _ hs ↦ (χ.LFunction_eq_mul_completedLFunction hs).symm⟩

theorem tendsto_const_mul_cpow_half (c : ℂ) :
    Tendsto (fun s : ℂ ↦ ((π : ℂ) ^ nrComplexPlaces K)⁻¹ * (χ.discrNormConductor : ℂ) ^ (s / 2))
      (𝓝[≠] c) (𝓝 (((π : ℂ) ^ nrComplexPlaces K)⁻¹ * (χ.discrNormConductor : ℂ) ^ (c / 2))) :=
  ((((differentiable_const _).mul ((differentiable_id.div_const 2).const_cpow
    (Or.inl (ofReal_ne_zero.2 χ.discrNormConductor_pos.ne')))).continuous.tendsto c).mono_left
      nhdsWithin_le_nhds)

section Trivial

variable {χ} {τ : ℝ}
  (hτ : ∀ x : IdeleGroup K, (χ.toIdele x : ℂ) = ((ideleModule K x : ℝ) : ℂ) ^ ((τ : ℂ) * I))
include hτ

theorem differentiableAt_completedLFunction_of_forall {s : ℂ} (hs₀ : s ≠ -((τ : ℂ) * I))
    (hs₁ : s ≠ 1 - (τ : ℂ) * I) : DifferentiableAt ℂ χ.completedLFunction s :=
  χ.differentiable_const_mul_cpow_half (differentiableAt_tateZeta hτ χ.testFunction_mem hs₀ hs₁)

theorem tendsto_mul_completedLFunction_neg_of_forall :
    Tendsto (fun s ↦ (s + (τ : ℂ) * I) * χ.completedLFunction s) (𝓝[≠] (-((τ : ℂ) * I)))
      (𝓝 (-(((normOneClassMeasure K univ).toReal : ℂ) * ((π : ℂ) ^ nrComplexPlaces K)⁻¹ *
        (χ.discrNormConductor : ℂ) ^ (-((τ : ℂ) * I) / 2)))) := by
  have h := (χ.tendsto_const_mul_cpow_half (-((τ : ℂ) * I))).mul
    (tendsto_mul_tateZeta_neg hτ χ.testFunction_mem)
  rw [testFunction_zero_of_forall hτ] at h
  refine (h.congr fun s ↦ ?_).trans (le_of_eq (congrArg 𝓝 (by ring)))
  rw [completedLFunction]
  ring

theorem adelicFourier_testFunction_zero_of_forall :
    adelicFourier K χ.testFunction 0 = χ.fourierConst χ.conductorDifferentIdele := by
  rw [χ.adelicFourier_testFunction χ.toFractionalIdeal_conductorDifferentIdele, smul_zero,
    testFunction_zero_of_forall (χ.inv_eq_cpow_of_forall hτ), mul_one]

theorem tendsto_mul_completedLFunction_one_sub_of_forall :
    Tendsto (fun s ↦ (s - (1 - (τ : ℂ) * I)) * χ.completedLFunction s) (𝓝[≠] (1 - (τ : ℂ) * I))
      (𝓝 (((normOneClassMeasure K univ).toReal : ℂ) * ((π : ℂ) ^ nrComplexPlaces K)⁻¹ *
        (χ.discrNormConductor : ℂ) ^ ((1 - (τ : ℂ) * I) / 2) *
          χ.fourierConst χ.conductorDifferentIdele)) := by
  have h := (χ.tendsto_const_mul_cpow_half (1 - (τ : ℂ) * I)).mul
    (tendsto_mul_tateZeta_one_sub hτ χ.testFunction_mem)
  rw [adelicFourier_testFunction_zero_of_forall hτ] at h
  refine (h.congr fun s ↦ ?_).trans (le_of_eq (congrArg 𝓝 (by ring)))
  rw [completedLFunction]
  ring

omit hτ in

theorem residue_one_sub_ne_zero :
    ((normOneClassMeasure K univ).toReal : ℂ) * ((π : ℂ) ^ nrComplexPlaces K)⁻¹ *
      (χ.discrNormConductor : ℂ) ^ ((1 - (τ : ℂ) * I) / 2) *
        χ.fourierConst χ.conductorDifferentIdele ≠ 0 :=
  mul_ne_zero (mul_ne_zero (mul_ne_zero
    (ofReal_ne_zero.2 (normOneClassMeasure_univ_toReal_ne_zero K))
    (inv_ne_zero pi_pow_nrComplexPlaces_ne_zero)) (χ.discrNormConductor_cpow_ne_zero _))
    (χ.fourierConst_ne_zero χ.toFractionalIdeal_conductorDifferentIdele)

theorem completedLFunction_eq_rootNumber_mul_of_forall {s : ℂ} (hs₀ : s ≠ -((τ : ℂ) * I))
    (hs₁ : s ≠ 1 - (τ : ℂ) * I) :
    χ.completedLFunction s = χ.rootNumber * χ⁻¹.completedLFunction (1 - s) := by
  refine χ.completedLFunction_eq_rootNumber_mul fun τ' hτ' ↦ ?_
  have h : τ' = τ := by
    rw [← archExponent_eq_of_forall hτ' (Classical.arbitrary _),
      archExponent_eq_of_forall hτ (Classical.arbitrary _)]
  subst h
  exact ⟨hs₀, hs₁⟩

theorem gammaFactor_neg_of_forall : χ.gammaFactor (-((τ : ℂ) * I)) = 0 := by
  refine Finset.prod_eq_zero (Finset.mem_univ (Classical.arbitrary (InfinitePlace K))) ?_
  unfold infiniteGamma
  rw [infiniteTau_of_forall hτ, infiniteWeight_of_forall hτ]
  split_ifs
  · rw [show -((τ : ℂ) * I) + (τ : ℂ) * I + ((0 : ℤ) : ℂ) = 0 by push_cast; ring]
    exact Gammaℝ_eq_zero_iff.2 ⟨0, by simp⟩
  · rw [show -((τ : ℂ) * I) + (τ : ℂ) * I + (((0 : ℤ).natAbs : ℕ) : ℂ) / 2 = 0 by push_cast; ring,
      Gammaℂ_def, Complex.Gamma_zero, mul_zero]

theorem exists_LFunction_continuation_of_forall :
    ∃ g : ℂ → ℂ, DifferentiableOn ℂ g {1 - (τ : ℂ) * I}ᶜ ∧
      (∀ s : ℂ, 1 < s.re → g s = χ.LFunction s) ∧
      ∃ r : ℂ, r ≠ 0 ∧ Tendsto (fun s ↦ (s - (1 - (τ : ℂ) * I)) * g s)
        (𝓝[≠] (1 - (τ : ℂ) * I)) (𝓝 r) := by
  set c : ℂ := -((τ : ℂ) * I) with hc
  set d : ℂ := 1 - (τ : ℂ) * I with hd
  set h : ℂ → ℂ := fun s ↦ (χ.discrNormConductor : ℂ) ^ (-(s / 2)) * (χ.gammaFactor s)⁻¹ with hh
  have hdiff : Differentiable ℂ h := χ.differentiable_cpow_mul_gammaFactor_inv
  have hcd : c ≠ d := fun h0 ↦ by
    have := congrArg re h0
    simp [hc, hd] at this
  have hhc : h c = 0 := by
    simp only [hh, hc, gammaFactor_neg_of_forall hτ, inv_zero, mul_zero]
  set g₀ : ℂ → ℂ := fun s ↦ h s * χ.completedLFunction s with hg₀
  set rc : ℂ := -(((normOneClassMeasure K univ).toReal : ℂ) * ((π : ℂ) ^ nrComplexPlaces K)⁻¹ *
    (χ.discrNormConductor : ℂ) ^ (-((τ : ℂ) * I) / 2)) with hrc

  have hres : Tendsto (fun s ↦ (s - c) * χ.completedLFunction s) (𝓝[≠] c) (𝓝 rc) := by
    refine (tendsto_mul_completedLFunction_neg_of_forall hτ).congr fun s ↦ ?_
    rw [hc, sub_neg_eq_add]
  have hslope : Tendsto (fun s ↦ (s - c)⁻¹ * h s) (𝓝[≠] c) (𝓝 (deriv h c)) := by
    refine (hasDerivAt_iff_tendsto_slope.1 (hdiff c).hasDerivAt).congr fun s ↦ ?_
    rw [slope_fun_def_field, hhc]
    beta_reduce
    rw [sub_zero, div_eq_inv_mul]
  have hlim : Tendsto g₀ (𝓝[≠] c) (𝓝 (deriv h c * rc)) := by
    refine (hslope.mul hres).congr' ?_
    filter_upwards [self_mem_nhdsWithin] with s hs
    have hs' : s - c ≠ 0 := sub_ne_zero.2 hs
    simp only [hg₀]
    field_simp
  set G : ℂ → ℂ := Function.update g₀ c (deriv h c * rc) with hG
  have hGeq : ∀ s, s ≠ c → G s = g₀ s := fun s hs ↦ Function.update_of_ne hs _ _
  refine ⟨G, ?_, fun s hs ↦ ?_, ?_⟩
  · have hnhds : ({d}ᶜ : Set ℂ) ∈ 𝓝 c := isOpen_compl_singleton.mem_nhds hcd
    refine (Complex.differentiableOn_compl_singleton_and_continuousAt_iff hnhds).1 ⟨?_, ?_⟩
    · refine DifferentiableOn.congr (fun z hz ↦ ?_) fun z hz ↦ hGeq z hz.2
      simp only [Set.mem_sdiff, mem_compl_iff, mem_singleton_iff] at hz
      exact ((hdiff z).mul (differentiableAt_completedLFunction_of_forall hτ hz.2 hz.1)).differentiableWithinAt
    · rw [hG, continuousAt_update_same]
      exact hlim
  · have hsc : s ≠ c := fun h0 ↦ by
      have := congrArg re h0
      simp [hc] at this
      linarith
    rw [hGeq s hsc, χ.LFunction_eq_mul_completedLFunction hs]
  · refine ⟨h d * (((normOneClassMeasure K univ).toReal : ℂ) * ((π : ℂ) ^ nrComplexPlaces K)⁻¹ *
      (χ.discrNormConductor : ℂ) ^ ((1 - (τ : ℂ) * I) / 2) *
        χ.fourierConst χ.conductorDifferentIdele), mul_ne_zero ?_ residue_one_sub_ne_zero, ?_⟩
    · exact mul_ne_zero (χ.discrNormConductor_cpow_ne_zero _) (inv_ne_zero (χ.gammaFactor_ne_zero
        (by simp [hd])))
    · have hh' : Tendsto h (𝓝[≠] d) (𝓝 (h d)) :=
        ((hdiff d).continuousAt.tendsto).mono_left nhdsWithin_le_nhds
      refine (hh'.mul (tendsto_mul_completedLFunction_one_sub_of_forall hτ)).congr' ?_
      have hne : ∀ᶠ s in 𝓝[≠] d, s ≠ c :=
        eventually_nhdsWithin_of_eventually_nhds (isOpen_compl_singleton.mem_nhds hcd.symm)
      filter_upwards [hne] with s hs
      rw [hGeq s hs]
      simp only [hg₀]
      ring

end Trivial

end HeckeCharacter

end

end GroundTheory.Global
