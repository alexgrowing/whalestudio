import Mathlib
import GroundTheory.GlobalFields.TateThesis.HeckeTheoremTrivial

open NumberField InfinitePlace IsDedekindDomain MeasureTheory Complex Topology Filter Set
open scoped NumberField.AdeleRing ComplexConjugate Real

namespace GroundTheory.Global

noncomputable section

variable {K : Type*} [Field K] [NumberField K]

open IdeleGroup

namespace HeckeCharacter

variable (χ : HeckeCharacter K)

def completedLFunction (s : ℂ) : ℂ :=
  ((π : ℂ) ^ nrComplexPlaces K)⁻¹ * (χ.discrNormConductor : ℂ) ^ (s / 2) *
    tateZeta χ.testFunction χ s

theorem discrNormConductor_cpow_ne_zero (s : ℂ) : (χ.discrNormConductor : ℂ) ^ s ≠ 0 := by
  rw [Ne, cpow_eq_zero_iff, not_and_or]
  exact Or.inl (ofReal_ne_zero.2 χ.discrNormConductor_pos.ne')

theorem completedLFunction_eq {s : ℂ} (hs : 1 < s.re) :
    χ.completedLFunction s =
      (χ.discrNormConductor : ℂ) ^ (s / 2) * χ.gammaFactor s * χ.LFunction s := by
  rw [completedLFunction, tateZeta_eq_globalZeta χ.testFunction_mem χ hs,
    χ.globalZeta_testFunction hs]
  have hπ := pi_pow_nrComplexPlaces_ne_zero (K := K)
  field_simp

theorem differentiable_const_mul_cpow_half {f : ℂ → ℂ} {s : ℂ} (hf : DifferentiableAt ℂ f s) :
    DifferentiableAt ℂ (fun s ↦ ((π : ℂ) ^ nrComplexPlaces K)⁻¹ *
      (χ.discrNormConductor : ℂ) ^ (s / 2) * f s) s :=
  ((differentiableAt_const _).mul ((differentiableAt_id.div_const 2).const_cpow
    (Or.inl (ofReal_ne_zero.2 χ.discrNormConductor_pos.ne')))).mul hf

def conductorDifferentIdele : (FiniteAdeleRing (𝓞 K) K)ˣ :=
  χ.exists_ofFinite_toFractionalIdeal_eq.choose

theorem toFractionalIdeal_conductorDifferentIdele :
    toFractionalIdeal (ofFinite χ.conductorDifferentIdele) =
      idealUnit χ.conductor χ.conductor_ne_bot * differentUnit :=
  χ.exists_ofFinite_toFractionalIdeal_eq.choose_spec

def rootNumber : ℂ :=
  χ.fourierConst χ.conductorDifferentIdele * (χ.toIdele (ofFinite χ.conductorDifferentIdele) : ℂ) *
    (χ.discrNormConductor : ℂ) ^ (1 / 2 : ℂ)

theorem completedLFunction_eq_rootNumber_mul_of_eq {s : ℂ}
    (h : tateZeta (adelicFourier K χ.testFunction) χ⁻¹ (1 - s) =
      χ.fourierConst χ.conductorDifferentIdele *
        (χ.toIdele (ofFinite χ.conductorDifferentIdele) : ℂ) *
        (χ.discrNormConductor : ℂ) ^ (1 - s) * tateZeta (χ⁻¹).testFunction χ⁻¹ (1 - s)) :
    χ.completedLFunction s = χ.rootNumber * χ⁻¹.completedLFunction (1 - s) := by
  have hA : (χ.discrNormConductor : ℂ) ≠ 0 := ofReal_ne_zero.2 χ.discrNormConductor_pos.ne'
  rw [completedLFunction, tateZeta_eq_tateZeta_one_sub χ.testFunction_mem, h, rootNumber,
    completedLFunction, discrNormConductor_inv]
  have hc : (χ.discrNormConductor : ℂ) ^ (s / 2) * (χ.discrNormConductor : ℂ) ^ (1 - s) =
      (χ.discrNormConductor : ℂ) ^ (1 / 2 : ℂ) * (χ.discrNormConductor : ℂ) ^ ((1 - s) / 2) := by
    rw [← cpow_add _ _ hA, ← cpow_add _ _ hA]
    congr 1
    ring
  linear_combination (((π : ℂ) ^ nrComplexPlaces K)⁻¹ * χ.fourierConst χ.conductorDifferentIdele *
    (χ.toIdele (ofFinite χ.conductorDifferentIdele) : ℂ) * tateZeta (χ⁻¹).testFunction χ⁻¹ (1 - s)) * hc

theorem completedLFunction_eq_rootNumber_mul {s : ℂ}
    (hs : ∀ τ : ℝ, (∀ x : IdeleGroup K,
      (χ.toIdele x : ℂ) = ((ideleModule K x : ℝ) : ℂ) ^ ((τ : ℂ) * I)) →
        s ≠ -((τ : ℂ) * I) ∧ s ≠ 1 - (τ : ℂ) * I) :
    χ.completedLFunction s = χ.rootNumber * χ⁻¹.completedLFunction (1 - s) := by
  refine χ.completedLFunction_eq_rootNumber_mul_of_eq ?_
  by_cases hχ : ∃ v : normOneSubgroup K, χ.toIdele (v : IdeleGroup K) ≠ 1
  · exact χ.tateZeta_adelicFourier_testFunction χ.toFractionalIdeal_conductorDifferentIdele hχ _
  · push Not at hχ
    obtain ⟨τ, hτ⟩ := (forall_normOne_eq_one_iff χ).1 hχ
    obtain ⟨h0, h1⟩ := hs τ hτ
    refine χ.tateZeta_adelicFourier_testFunction_of_forall
      χ.toFractionalIdeal_conductorDifferentIdele hτ (fun h ↦ h1 ?_) (fun h ↦ h0 ?_)
    · linear_combination -h
    · linear_combination -h

theorem completedLFunction_eq_rootNumber_mul_of_not
    (hχ : ¬ ∃ τ : ℝ, ∀ x : IdeleGroup K,
      (χ.toIdele x : ℂ) = ((ideleModule K x : ℝ) : ℂ) ^ ((τ : ℂ) * I)) (s : ℂ) :
    χ.completedLFunction s = χ.rootNumber * χ⁻¹.completedLFunction (1 - s) :=
  χ.completedLFunction_eq_rootNumber_mul fun τ hτ ↦ absurd ⟨τ, hτ⟩ hχ

theorem two_ne_pole (τ : ℝ) : (2 : ℂ) ≠ -((τ : ℂ) * I) ∧ (2 : ℂ) ≠ 1 - (τ : ℂ) * I := by
  constructor <;> intro h <;> have := congrArg re h <;> simp at this

theorem neg_one_ne_pole (τ : ℝ) :
    (-1 : ℂ) ≠ -((τ : ℂ) * I) ∧ (-1 : ℂ) ≠ 1 - (τ : ℂ) * I := by
  constructor <;> intro h <;> have := congrArg re h <;> simp at this <;> norm_num at this

theorem completedLFunction_two_ne_zero : χ.completedLFunction 2 ≠ 0 := by
  rw [χ.completedLFunction_eq (by norm_num)]
  exact mul_ne_zero (mul_ne_zero (χ.discrNormConductor_cpow_ne_zero _)
    (χ.gammaFactor_ne_zero (by norm_num))) (χ.LFunction_ne_zero (by norm_num))

theorem rootNumber_mul_rootNumber_inv : χ.rootNumber * χ⁻¹.rootNumber = 1 := by
  have h1 := χ.completedLFunction_eq_rootNumber_mul (s := 2) fun τ _ ↦ two_ne_pole τ
  have h2 := χ⁻¹.completedLFunction_eq_rootNumber_mul (s := -1) fun τ _ ↦ neg_one_ne_pole τ
  rw [inv_inv, show (1 : ℂ) - -1 = 2 by norm_num] at h2
  rw [show (1 : ℂ) - 2 = -1 by norm_num, h2, ← mul_assoc] at h1
  exact mul_right_cancel₀ χ.completedLFunction_two_ne_zero (h1.symm.trans (one_mul _).symm)

end HeckeCharacter

end

end GroundTheory.Global
