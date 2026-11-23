import Mathlib
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.InvariantFunctionsDescend
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DataRigidTorsionOfDataRigid
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem eq_one_of_fibre_const_of_section :
    GlobalFnsSt → ∀ (S : Scheme.{0}) (B W : Over S) [GrpObj B], IsAbelianScheme B → ∀ (π : W ⟶ B) [Flat π.left] [Surjective π.left] [QuasiCompact π.left] (ρ : Γ(W.left, ⊤)) (σ : 𝟙_ (Over S) ⟶ W), (∀ (Z : Over S) (g₁ g₂ : Z ⟶ W), g₁ ≫ π = g₂ ≫ π → g₁.left.appTop.hom ρ = g₂.left.appTop.hom ρ) → σ.left.appTop.hom ρ = 1 → ρ = 1 := by
  intro hG S B W _ hB π _ _ _ ρ σ h hσ
  obtain ⟨a, rfl⟩ := FunDescent.exists_appTop_eq π.left ρ (by
    intro Z g₁ g₂ e
    let Z' : Over S := Over.mk (g₂ ≫ W.hom)
    let k₂ : Z' ⟶ W := Over.homMk g₂ rfl
    let k₁ : Z' ⟶ W := Over.homMk g₁ (by
      change g₁ ≫ W.hom = g₂ ≫ W.hom
      rw [← Over.w π, reassoc_of% e])
    exact h Z' k₁ k₂ (Over.OverMorphism.ext e))
  obtain ⟨s, rfl⟩ := (hG S B hB).2 a
  rw [← FunDescent.comp_appTop_apply, ← FunDescent.comp_appTop_apply, Category.assoc, Over.w π,
    Over.w σ] at hσ
  have hs : s = 1 := by
    have e : (𝟙_ (Over S)).hom = 𝟙 S := rfl
    rw [e] at hσ
    simpa using hσ
  rw [hs, map_one, map_one]

end GlobalTheory
