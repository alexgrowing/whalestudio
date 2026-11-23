import Mathlib
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsSystem
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsHeatZero
open Matrix Complex NumberField MeasureTheory GlobalTheory GlobalTheory.SW GlobalTheory.ThFr ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open scoped ComplexConjugate ComplexOrder Real Classical

namespace GlobalTheory.SW

theorem summable_setIntegral_of_summable_norm {I Y : Type} [MeasurableSpace Y] (ν : Measure Y)
    (D : I → Set Y) (f : I → Y → ℂ) (h : Summable fun i => ∫ y in D i, ‖f i y‖ ∂ν) :
    Summable fun i => ∫ y in D i, f i y ∂ν := by

  exact Summable.of_norm_bounded h fun i => norm_integral_le_integral_norm _

def finiteRankDomain {I Y : Type} [MeasurableSpace Y] (ν : Measure Y) (D : I → Set Y) {m : ℕ}
    (t : Fin m → I → Y → ℂ) : Submodule ℂ (Fin m → ℂ) where
  carrier := {v | (∀ i, IntegrableOn (fun y => ∑ j, v j * t j i y) (D i) ν) ∧
    Summable fun i => ∫ y in D i, ‖∑ j, v j * t j i y‖ ∂ν}
  zero_mem' := by
    refine ⟨fun i => ?_, ?_⟩
    · simp
    · simp
  add_mem' := by
    rintro v w ⟨hv, hv'⟩ ⟨hw, hw'⟩
    have key : ∀ i y, ∑ j, (v + w) j * t j i y = ∑ j, v j * t j i y + ∑ j, w j * t j i y := by
      intro i y
      simp [add_mul, Finset.sum_add_distrib]
    refine ⟨fun i => ?_, ?_⟩
    · simp only [key]
      exact (hv i).add (hw i)
    · simp only [key]
      refine Summable.of_nonneg_of_le (fun i => integral_nonneg fun y => norm_nonneg _)
        (fun i => ?_) (hv'.add hw')
      rw [← integral_add (hv i).norm (hw i).norm]
      exact integral_mono ((hv i).add (hw i)).norm ((hv i).norm.add (hw i).norm)
        (fun y => norm_add_le _ _)
  smul_mem' := by
    rintro c v ⟨hv, hv'⟩
    have key : ∀ i y, ∑ j, (c • v) j * t j i y = c * ∑ j, v j * t j i y := by
      intro i y
      simp [Finset.mul_sum, mul_assoc]
    refine ⟨fun i => ?_, ?_⟩
    · simp only [key]
      exact (hv i).const_mul c
    · simp only [key, norm_mul, integral_const_mul]
      exact hv'.mul_left _

noncomputable def finiteRankFunctional {I Y : Type} [MeasurableSpace Y] (ν : Measure Y)
    (D : I → Set Y) {m : ℕ} (t : Fin m → I → Y → ℂ) : finiteRankDomain ν D t →ₗ[ℂ] ℂ where
  toFun v := ∑' i, ∫ y in D i, ∑ j, v.1 j * t j i y ∂ν
  map_add' := by
    rintro ⟨v, hv, hv'⟩ ⟨w, hw, hw'⟩
    have key : ∀ i y, ∑ j, (v + w) j * t j i y = ∑ j, v j * t j i y + ∑ j, w j * t j i y := by
      intro i y
      simp [add_mul, Finset.sum_add_distrib]
    show ∑' i, ∫ y in D i, ∑ j, (v + w) j * t j i y ∂ν
      = ∑' i, ∫ y in D i, ∑ j, v j * t j i y ∂ν + ∑' i, ∫ y in D i, ∑ j, w j * t j i y ∂ν
    rw [← Summable.tsum_add (summable_setIntegral_of_summable_norm ν D _ hv')
      (summable_setIntegral_of_summable_norm ν D _ hw')]
    refine tsum_congr fun i => ?_
    simp only [key]
    exact integral_add (hv i) (hw i)
  map_smul' := by
    rintro c ⟨v, hv⟩
    have key : ∀ i y, ∑ j, (c • v) j * t j i y = c * ∑ j, v j * t j i y := by
      intro i y
      simp [Finset.mul_sum, mul_assoc]
    show ∑' i, ∫ y in D i, ∑ j, (c • v) j * t j i y ∂ν
      = c * ∑' i, ∫ y in D i, ∑ j, v j * t j i y ∂ν
    simp only [key, integral_const_mul]
    exact tsum_mul_left

theorem finiteRank_integral_mem_span : ∀ (A I Y : Type) [Countable I] [MeasurableSpace Y] (ν : Measure Y) (D : I → Set Y) (S : Set A) (m : ℕ) (e : Fin m → A → ℂ) (t : Fin m → I → Y → ℂ), (∀ a ∈ S, (∀ i, IntegrableOn (fun y => ∑ j, e j a * t j i y) (D i) ν) ∧ Summable fun i => ∫ y in D i, ‖∑ j, e j a * t j i y‖ ∂ν) → ∃ b : Fin m → ℂ, ∀ a ∈ S, ∑' i, ∫ y in D i, ∑ j, e j a * t j i y ∂ν = ∑ j, b j * e j a := by
  intro A I Y _ _ ν D S m e t hS

  obtain ⟨g, hg⟩ := LinearMap.exists_extend (finiteRankFunctional ν D t)
  refine ⟨fun j => g (Pi.single j 1), fun a ha => ?_⟩
  have hmem : (fun j => e j a) ∈ finiteRankDomain ν D t := hS a ha
  have h1 : g (fun j => e j a) = ∑' i, ∫ y in D i, ∑ j, e j a * t j i y ∂ν :=
    LinearMap.congr_fun hg ⟨fun j => e j a, hmem⟩
  rw [← h1]
  have hx : (fun j => e j a) = ∑ j, e j a • (Pi.single j (1 : ℂ) : Fin m → ℂ) := by
    ext k
    simp [Pi.single_apply]
  rw [hx, map_sum]
  simp [mul_comm]

end GlobalTheory.SW
