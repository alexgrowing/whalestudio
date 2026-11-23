import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDefiniteDatumGoodObj
import Development.AbelianVarietyTheory.Definitions.Divisors.IsKSValueOneOfRetraction

noncomputable section

namespace GlobalTheory.UPel.Sm

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel

variable {F : Type} [Field F] [NumberField F] [IsCMField F]

def InfUniv {D : Datum F} {p N : ℕ} {X : Scheme.{0}} {s : X ⟶ Sp (D.OEp p)} (univ : Obj D p N s) : Prop :=
  ∀ (C C₀ : Type) [CommRing C] [IsLocalRing C] [IsArtinianRing C] [CommRing C₀] (π : C →+* C₀),
    Function.Surjective π → RingHom.ker π ^ 2 = ⊥ →
    ∀ (t : Sp C ⟶ Sp (D.OEp p)) (o : Obj D p N t) (o₀ : Obj D p N (spMap π ≫ t)) (x₀ : Sp C₀ ⟶ X),
      x₀ ≫ s = spMap π ≫ t → Nonempty (ObjMap o₀ o (spMap π)) → Nonempty (ObjMap o₀ univ x₀) →
      ∃! x : Sp C ⟶ X, spMap π ≫ x = x₀ ∧ x ≫ s = t ∧ Nonempty (ObjMap o univ x)

section KS

variable {k H O : Type*} [Field k] [AddCommGroup H] [Module k H] [Ring O]

def IsKS (ρ : O →+* Module.End k H) (φ : LinearMap.BilinForm k H) (Fil Z : Submodule k H)
    (f : H →ₗ[k] H) : Prop :=
  (∀ a, ∀ x ∈ Fil, f (ρ a x) - ρ a (f x) ∈ Fil) ∧ (∀ x ∈ Z, f x ∈ Fil) ∧
    ∀ x ∈ Fil, ∀ y ∈ Fil, φ (f x) y + φ x (f y) = 0

def KSDim (ρ : O →+* Module.End k H) (φ : LinearMap.BilinForm k H) (Fil Z : Submodule k H) (d : ℕ) :
    Prop :=
  ∃ f : Fin d → (H →ₗ[k] H), (∀ i, IsKS ρ φ Fil Z (f i)) ∧
    ∀ g, IsKS ρ φ Fil Z g → ∃! c : Fin d → k, ∀ x ∈ Fil, g x - ∑ i, c i • f i x ∈ Fil

end KS

end GlobalTheory.UPel.Sm
