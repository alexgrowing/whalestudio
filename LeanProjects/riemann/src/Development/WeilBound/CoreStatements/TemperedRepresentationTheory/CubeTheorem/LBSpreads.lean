import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.CubeTheorem.SchemeModels
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.AbLaw

namespace GlobalTheory.SpreadingModels

def PerfAll : Prop :=
  ∀ (R : Type) [CommRing R] (Y : Scheme.{0}) (f : Y ⟶ Spec (CommRingCat.of R)), Smooth f → IsProper f →
    ∀ M : LB Y, M.IsLB → Nonempty (Perf f M)

def HasModel {R : Type} [CommRing R] {Y : Scheme.{0}} (f : Y ⟶ Spec (CommRingCat.of R)) (M : LB Y) : Prop :=
  ∃ (R₀ : Type) (_ : CommRing R₀) (_ : IsNoetherianRing R₀) (φ : R₀ →+* R) (Y₀ : Scheme.{0})
    (f₀ : Y₀ ⟶ Spec (CommRingCat.of R₀)) (π : Y ⟶ Y₀),
    IsProper f₀ ∧ Flat f₀ ∧ IsPullback π f f₀ (Spec.map (CommRingCat.ofHom φ)) ∧
      ∃ M₀ : LB Y₀, M₀.IsLB ∧ ∃ w : LB.Iso M (M₀.pull π), w.IsGen

def LBSpreads : Prop :=
  ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (φ : R₀ →+* R) (Y Y₀ : Scheme.{0})
    (f : Y ⟶ Spec (CommRingCat.of R)) (f₀ : Y₀ ⟶ Spec (CommRingCat.of R₀)) (π : Y ⟶ Y₀),
    IsModel φ f f₀ π → ∀ M : LB Y, M.IsLB →
      ∃ (R₁ : Type) (_ : CommRing R₁) (ψ : R₀ →+* R₁) (φ₁ : R₁ →+* R)
        (ρ : Y ⟶ pullback f₀ (Spec.map (CommRingCat.ofHom ψ))),
        φ₁.comp ψ = φ ∧ Algebra.FiniteType ℤ R₁ ∧ ρ ≫ pullback.fst _ _ = π ∧
          ρ ≫ pullback.snd _ _ = f ≫ Spec.map (CommRingCat.ofHom φ₁) ∧
          ∃ M₁ : LB (pullback f₀ (Spec.map (CommRingCat.ofHom ψ))), M₁.IsLB ∧
            ∃ w : LB.Iso M (M₁.pull ρ), w.IsGen

end GlobalTheory.SpreadingModels
