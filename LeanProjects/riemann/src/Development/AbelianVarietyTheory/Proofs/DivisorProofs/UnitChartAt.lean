import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapPairDetCovec

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete

namespace GlobalTheory.FlatModel

def UnitChartAt (p : ℕ) [Fact p.Prime] {X : Scheme.{0}} (Xw : X.Opens) (K : (Sp 𝓞_ℂ_[p] ⟶ X) → Set ℂ_[p]) (x : X) :
    Prop :=
  ∃ (R : Type) (_ : CommRing R) (ξ : Sp R ⟶ X) (c : (Localization.Away (p : R))ˣ), IsOpenImmersion ξ ∧
    x ∈ Set.range ξ ∧ ∀ φ : R →+* 𝓞_ℂ_[p], IsTest p Xw (spMap φ ≫ ξ) →
      ∀ ψ : Localization.Away (p : R) →+* ℂ_[p], ψ.comp (algebraMap R _) = (algebraMap 𝓞_ℂ_[p] ℂ_[p]).comp φ →
        ∀ κ ∈ K (spMap φ ≫ ξ), ‖ψ (c : Localization.Away (p : R)) - κ‖ < ‖κ‖

def DensSt : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (V : ValuationSubring F) (p : ℕ) [Fact p.Prime], (p : F) ∈ V.nonunits →
    ∀ (X : Scheme.{0}) (s : X ⟶ Sp V) (Xw : X.Opens), IsIntegral X → Flat s → LocallyOfFiniteType s →
      Xw ≤ X.basicOpen (p : Γ(X, ⊤)) → (Xw : Set X).Nonempty →
      ∀ (R : Type) [CommRing R] (ξ : Sp R ⟶ X), IsOpenImmersion ξ →
        (∃ x ∈ Set.range ξ, x ∉ X.basicOpen (p : Γ(X, ⊤))) → ∃ φ : R →+* 𝓞_ℂ_[p], IsTest p Xw (spMap φ ≫ ξ)

def RestrictSt : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (V : ValuationSubring F) (p : ℕ) [Fact p.Prime], (p : F) ∈ V.nonunits →
    ∀ (X : Scheme.{0}) (s : X ⟶ Sp V) (Xw : X.Opens), ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme X → IsProjOver s → Flat s →
      Xw ≤ X.basicOpen (p : Γ(X, ⊤)) → GeomIrr s Xw → ∀ (n : ℕ) (K : (Sp 𝓞_ℂ_[p] ⟶ X) → Set ℂ_[p]),
      (∀ yb, IsTest p Xw yb → (K yb).Nonempty) → (∀ x ∈ closure (Xw : Set X), ChartAt p n Xw K x) →
      ∃ (X₁ : Scheme.{0}) (s₁ : X₁ ⟶ Sp V) (Xw₁ : X₁.Opens) (K₁ : (Sp 𝓞_ℂ_[p] ⟶ X₁) → Set ℂ_[p]),
        IsIntegral X₁ ∧ ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme X₁ ∧ IsProjOver s₁ ∧ Flat s₁ ∧
        Xw₁ ≤ X₁.basicOpen (p : Γ(X₁, ⊤)) ∧ GeomIrr s₁ Xw₁ ∧ (∀ yb, IsTest p Xw₁ yb → (K₁ yb).Nonempty) ∧
        (∀ x : X₁, ChartAt p n Xw₁ K₁ x) ∧
        ∀ yb, IsTest p Xw yb → ∃ yb₁, IsTest p Xw₁ yb₁ ∧ K yb ⊆ K₁ yb₁

def ModSt : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (V : ValuationSubring F) (p : ℕ) [Fact p.Prime], (p : F) ∈ V.nonunits →
    ∀ (X : Scheme.{0}) (s : X ⟶ Sp V) (Xw : X.Opens), IsIntegral X → ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme X →
      IsProjOver s → Flat s → Xw ≤ X.basicOpen (p : Γ(X, ⊤)) → GeomIrr s Xw →
      ∀ (n : ℕ) (K : (Sp 𝓞_ℂ_[p] ⟶ X) → Set ℂ_[p]),
      (∀ yb, IsTest p Xw yb → (K yb).Nonempty) → (∀ x : X, ChartAt p n Xw K x) →
      ∃ (X' : Scheme.{0}) (s' : X' ⟶ Sp V) (Xw' : X'.Opens) (K' : (Sp 𝓞_ℂ_[p] ⟶ X') → Set ℂ_[p]),
        IsIntegral X' ∧ ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme X' ∧ IsProjOver s' ∧ Flat s' ∧
        Xw' ≤ X'.basicOpen (p : Γ(X', ⊤)) ∧ GeomIrr s' Xw' ∧ (∀ yb, IsTest p Xw' yb → (K' yb).Nonempty) ∧
        (∀ x : X', UnitChartAt p Xw' K' x) ∧
        ∀ yb, IsTest p Xw yb → ∃ yb', IsTest p Xw' yb' ∧ K yb ⊆ K' yb'

def PrincSt : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (V : ValuationSubring F) (p : ℕ) [Fact p.Prime], (p : F) ∈ V.nonunits →
    ∀ (X : Scheme.{0}) (s : X ⟶ Sp V) (Xw : X.Opens), IsIntegral X → ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme X →
      IsProjOver s → Flat s → Xw ≤ X.basicOpen (p : Γ(X, ⊤)) → GeomIrr s Xw →
      ∀ (K : (Sp 𝓞_ℂ_[p] ⟶ X) → Set ℂ_[p]),
      (∀ yb, IsTest p Xw yb → (K yb).Nonempty) → (∀ x : X, UnitChartAt p Xw K x) →
      ∃ ρ : ℝ, ∀ yb, IsTest p Xw yb → ∀ κ ∈ K yb, ‖κ‖ = ρ

end GlobalTheory.FlatModel
