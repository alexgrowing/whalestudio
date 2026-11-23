import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapPairDetCovec
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteGaloisInertiaLiftsAbsoluteInertiaRat

open CategoryTheory Limits AlgebraicGeometry NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.CompHt GlobalTheory.AllWt

namespace GlobalTheory.PlaceExt

theorem valuation_lt_one_iff_inv {L : Type*} [Field L] (V : ValuationSubring L) (y : L) :
    V.valuation y < 1 ↔ y = 0 ∨ y⁻¹ ∉ V := by
  rcases eq_or_ne y 0 with rfl | hy
  · simp
  · have hpos : 0 < V.valuation y := zero_lt_iff.2 ((map_ne_zero _).2 hy)
    rw [← V.valuation_le_one_iff, map_inv₀, not_le, one_lt_inv₀ hpos]
    simp [hy]

theorem exists_lift {L M C : Type*} [Field L] [Field M] [Algebra L M] [Algebra.IsAlgebraic L M] [Field C]
    [IsAlgClosed C] (f : L →+* C) : ∃ h : M →+* C, ∀ x, h (algebraMap L M x) = f x := by
  letI := f.toAlgebra
  exact ⟨(IsAlgClosed.lift : M →ₐ[L] C), fun x => (IsAlgClosed.lift : M →ₐ[L] C).commutes x⟩

theorem exists_extend_compatible : ∀ (F F' : IntermediateField ℚ ℂ) (hle : F ≤ F'), FiniteDimensional ℚ F' →
    ∀ (W : ValuationSubring ℂ) (K : Type) [Field K] [IsAlgClosed K] (O : ValuationSubring K) (g : F →+* K),
    (∀ x : F, (x : ℂ) ∈ W ↔ g x ∈ O) → ∃ g' : F' →+* K, (∀ x : F, g' (IntermediateField.inclusion hle x) = g x) ∧
      ∀ x : F', (x : ℂ) ∈ W → g' x ∈ O := by
  intro F F' hle hfin W K _ _ O g hg
  haveI : FiniteDimensional ℚ F :=
    FiniteDimensional.of_injective (IntermediateField.inclusion hle).toLinearMap
      (IntermediateField.inclusion hle).injective
  haveI : NumberField F := ⟨⟩
  letI : Algebra F F' := (IntermediateField.inclusion hle).toRingHom.toAlgebra
  haveI : IsScalarTower ℚ F F' := IsScalarTower.of_algebraMap_eq' (Subsingleton.elim _ _)
  haveI : Algebra.IsAlgebraic F F' := Algebra.IsAlgebraic.tower_top (K := ℚ) F
  let Ω := AlgebraicClosure F'
  haveI : Algebra.IsAlgebraic F Ω := Algebra.IsAlgebraic.trans F F' Ω
  haveI : IsAlgClosure F Ω := ⟨inferInstance, inferInstance⟩
  obtain ⟨g₀, hg₀⟩ := exists_lift (M := F') g
  obtain ⟨ι₂, hι₂⟩ := exists_lift (M := Ω) g₀
  obtain ⟨ι₁, hι₁⟩ := exists_lift (M := Ω) (algebraMap F' ℂ)
  have k₁ : ∀ y : F, ι₁ (algebraMap F Ω y) = (y : ℂ) := fun y => by
    rw [IsScalarTower.algebraMap_apply F F' Ω, hι₁]; rfl
  have k₂ : ∀ y : F, ι₂ (algebraMap F Ω y) = g y := fun y => by
    rw [IsScalarTower.algebraMap_apply F F' Ω, hι₂, hg₀]
  let A := W.comap ι₁
  let A' := O.comap ι₂
  have h : ∀ x : 𝓞 F, A.valuation (algebraMap F Ω x) < 1 ↔ A'.valuation (algebraMap F Ω x) < 1 := by
    intro x
    generalize (x : F) = y
    rw [valuation_lt_one_iff_inv, valuation_lt_one_iff_inv, ValuationSubring.mem_comap,
      ValuationSubring.mem_comap, ← map_inv₀, k₁, k₂, hg]
  obtain ⟨σ, hσ⟩ := GlobalTheory.InertiaLift.exists_smul_eq (F := F) (Ω := Ω) h
  refine ⟨ι₂.comp (σ.toRingEquiv.toRingHom.comp (algebraMap F' Ω)), fun x => ?_, fun x hx => ?_⟩
  · change ι₂ (σ (algebraMap F' Ω (algebraMap F F' x))) = g x
    rw [← IsScalarTower.algebraMap_apply, σ.commutes, k₂]
  · change ι₂ (σ (algebraMap F' Ω x)) ∈ O
    by_contra hn
    have h1 : A'.valuation (σ (algebraMap F' Ω x)⁻¹) < 1 := by
      rw [valuation_lt_one_iff_inv, map_inv₀, inv_inv]
      exact Or.inr hn
    rcases (valuation_lt_one_iff_inv _ _).1 ((hσ _).1 h1) with h2 | h2
    · have : x = 0 := by simpa using h2
      subst this
      exact hn (by simp)
    · apply h2
      rw [inv_inv, ValuationSubring.mem_comap, hι₁]
      exact hx

end GlobalTheory.PlaceExt
