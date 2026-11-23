import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.AdelicGroupAlgebraActionInjective
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsHTFormOver
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PushInvertible
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GlueApplyOfNotInFibre
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsHodgeLine

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar.LieBaseAct

theorem baseChange_act : ∀ (X X' : Scheme.{0}) (Ω Ω' : Type) [Field Ω] [Field Ω'] (ξ : Sp Ω ⟶ X) (ξ' : Sp Ω' ⟶ X') (f : X' ⟶ X) (i : Ω →+* Ω') (G : Over X) (G' : Over X') [GrpObj G] [GrpObj G'] (φ : G'.left ⟶ G.left) (V V' : Type) [AddCommGroup V] [Module Ω V] [AddCommGroup V'] [Module Ω' V'] (M : LieModel G ξ V) (M' : LieModel G' ξ' V') (j : V →+ V') (O : Type) [CommRing O] (act : O → (G ⟶ G)) (act' : O → (G' ⟶ G')) (ρ : O →+* Module.End Ω V) (ρ' : O →+* Module.End Ω' V'), GlobalTheory.CompanionTheory.Ar.Dominates ξ' ξ f i → IsGrpPullback G' G f φ → (∀ e, (M'.pt (j e)).left ≫ φ = Spec.map (CommRingCat.ofHom (dualMap i)) ≫ (M.pt e).left) → M.IsActOf act ρ → M'.IsActOf act' ρ' → (∀ a, (act' a).left ≫ φ = φ ≫ (act a).left) → ∀ a e, ρ' a (j e) = j (ρ a e) := by
  intro X X' Ω Ω' _ _ ξ ξ' f i G G' _ _ φ V V' _ _ _ _ M M' j O _ act act' ρ ρ' _ hpb hpt hM hM' hcomm a e
  apply M'.inj
  rw [hM' a (j e)]
  apply Over.OverMorphism.ext
  apply hpb.1.hom_ext
  · simp only [Over.comp_left, Category.assoc, hcomm a]
    rw [← Category.assoc, hpt e, hpt (ρ a e), hM a e, Over.comp_left]
    simp only [Category.assoc]
  · rw [Over.w, Over.w]

end GlobalTheory.CompanionTheory.Ar.LieBaseAct
