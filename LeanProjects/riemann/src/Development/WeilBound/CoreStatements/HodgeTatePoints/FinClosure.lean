import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GlueApplyOfNotInFibre
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsGenericFlag
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.LatNormGrLatNeZeroOfSpan
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
import GroundTheory.HeightsAndTheta.Heights.IntegralModels.PFiniteIntegralClosure

open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar NumberField

namespace PositivityTheory.HtPt.Mb

theorem fin_closure : ∀ (A : Type) [CommRing A] [IsDomain A] [Algebra.EssFiniteType ℤ A] (K : Type) [Field K] [Algebra A K] [IsFractionRing A K] (L : Type) [Field L] [Algebra K L] [FiniteDimensional K L] [Algebra A L] [IsScalarTower A K L], Module.Finite A (integralClosure A L) := by
  intro A _ _ _ K _ _ _ L _ _ _ _ _
  let A₀ := Algebra.EssFiniteType.subalgebra ℤ A
  let S := Algebra.EssFiniteType.submonoid ℤ A
  have hS : ∀ a : A, ∃ u s : A₀, IsUnit (s : A) ∧ a * s = u := fun a => by
    obtain ⟨⟨u, s⟩, e⟩ := IsLocalization.surj S a
    exact ⟨u, s, IsLocalization.map_units A s, e⟩
  have : FaithfulSMul A₀ K := (faithfulSMul_iff_algebraMap_injective _ _).2
    ((IsFractionRing.injective A K).comp Subtype.val_injective)
  have : IsFractionRing A₀ K := IsFractionRing.of_field _ _ fun z => by
    obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := A) z
    obtain ⟨u, s, hs, e⟩ := hS a
    obtain ⟨v, t, ht, e'⟩ := hS b
    refine ⟨u * t, v * s, ?_⟩
    have h1 : algebraMap A K s ≠ 0 := (hs.map _).ne_zero
    have h2 : algebraMap A K t ≠ 0 := (ht.map _).ne_zero
    show _ = algebraMap A K (u * t) / algebraMap A K (v * s)
    rw [← e, ← e']
    simp only [map_mul]
    rw [mul_assoc, mul_assoc, mul_comm (algebraMap A K t), mul_div_mul_right _ _ (mul_ne_zero h1 h2)]
  have hfin : Module.Finite A₀ (integralClosure A₀ L) :=
    GroundTheory.Heights₂.Heights.Model.FiniteIntegralClosure.proof A₀ K L
  obtain ⟨g, hg⟩ : (Subalgebra.toSubmodule (integralClosure A₀ L)).FG := Module.Finite.iff_fg.1 hfin
  refine (Module.Finite.iff_fg (N := Subalgebra.toSubmodule (integralClosure A L))).2 ⟨g, le_antisymm ?_ ?_⟩
  · refine Submodule.span_le.2 fun y hy => ?_
    have h : y ∈ Subalgebra.toSubmodule (integralClosure A₀ L) := hg ▸ Submodule.subset_span hy
    exact IsIntegral.tower_top (R := A₀) h
  · intro y hy
    obtain ⟨m, hm⟩ := IsIntegral.exists_multiple_integral_of_isLocalization S y (hy : IsIntegral A y)
    have h : m • y ∈ Submodule.span A₀ (g : Set L) := by
      rw [hg]
      exact hm
    have h' : (m.1 : A) • y ∈ Submodule.span A (g : Set L) := Submodule.span_le_restrictScalars A₀ A _ h
    obtain ⟨w, hw⟩ := (IsLocalization.map_units A m).exists_left_inv
    have := Submodule.smul_mem _ w h'
    have hw' : w * (m.1 : A) = 1 := hw
    rwa [smul_smul, hw', one_smul] at this

end PositivityTheory.HtPt.Mb
