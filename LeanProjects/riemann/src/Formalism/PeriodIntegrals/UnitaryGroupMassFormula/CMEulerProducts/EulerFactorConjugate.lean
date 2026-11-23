import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CMEulerProducts.StepRegroup

open NumberField

noncomputable section

namespace CMEul

open Formalism.L2.SG.MassRatio Formalism.HermitianLatticesTheory

theorem euler_factor_conjugate : StepConj := by
  intro F E _ _ _ _ _ _ hFE
  obtain ⟨hE, hR⟩ := hFE
  let σ : 𝓞 E ≃+* 𝓞 E := RingOfIntegers.mapRingEquiv (starRingAut (R := E))
  have hσ : ∀ x : 𝓞 E, algebraMap (𝓞 E) E (σ x) = star (algebraMap (𝓞 E) E x) := fun x => rfl
  have hσσ : ∀ x : 𝓞 E, σ (σ x) = x := by
    intro x
    apply RingOfIntegers.ext
    change algebraMap (𝓞 E) E (σ (σ x)) = algebraMap (𝓞 E) E x
    rw [hσ, hσ, star_star]
  refine ⟨σ, hσ, hσσ, ?_, ?_, ?_⟩
  · intro P
    unfold conjIdeal
    change _ = Ideal.span (σ '' P)
    congr 1
    ext r
    constructor
    · rintro ⟨s, hs, hrs⟩
      refine ⟨s, hs, ?_⟩
      apply RingOfIntegers.ext
      change algebraMap (𝓞 E) E (σ s) = algebraMap (𝓞 E) E r
      rw [hσ, hrs]
    · rintro ⟨s, hs, rfl⟩
      exact ⟨s, hs, hσ s⟩
  · intro x
    constructor
    · intro hx
      have hfix : algebraMap (𝓞 E) E x ∈ {a : E | star a = a} := by
        change star (algebraMap (𝓞 E) E x) = algebraMap (𝓞 E) E x
        rw [← hσ, hx]
      rw [← hR] at hfix
      obtain ⟨y, hy⟩ := hfix
      have hyint : IsIntegral ℤ y := by
        have h1 : IsIntegral ℤ ((algebraMap F E).toIntAlgHom y) := by
          rw [RingHom.toIntAlgHom_coe, hy]
          exact RingOfIntegers.isIntegral_coe x
        exact (isIntegral_algHom_iff _ (algebraMap F E).injective).mp h1
      refine ⟨⟨y, hyint⟩, ?_⟩
      apply RingOfIntegers.ext
      exact hy
    · rintro ⟨z, rfl⟩
      apply RingOfIntegers.ext
      change algebraMap (𝓞 E) E (σ (algebraMap (𝓞 F) (𝓞 E) z)) =
        algebraMap (𝓞 E) E (algebraMap (𝓞 F) (𝓞 E) z)
      rw [hσ]
      have hmem : algebraMap (𝓞 E) E (algebraMap (𝓞 F) (𝓞 E) z) ∈ Set.range (algebraMap F E) :=
        ⟨(z : F), rfl⟩
      rw [hR] at hmem
      exact hmem
  · intro P hP
    obtain ⟨θ, t, ht, hθt⟩ := hE.2.2 P hP
    refine ⟨θ, ?_⟩
    have : σ θ = t := by
      apply RingOfIntegers.ext
      change algebraMap (𝓞 E) E (σ θ) = algebraMap (𝓞 E) E t
      rw [hσ, ht]
    rw [this]
    exact hθt

end CMEul
