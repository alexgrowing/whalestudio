import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HasDivPlace
import Development.AbelianVarietyTheory.Definitions.Divisors.PointsNonemptyUnitaryRankOne

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField Matrix
open IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct Classical ComplexOrder
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.DiscreteGroups.LocalClassField
open GlobalTheory GlobalTheory.AV GlobalTheory.AV.AbVar GlobalTheory.PDivGroup GlobalTheory.Dieu GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKGeo
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.LKCx

def PrimeToP {p : ℕ} [Fact p.Prime] {D : Datum p} {R : Type} [CommRing R] {b : Base D R} {k : Type} [Field k]
    {β : R →+* k} {N : ℕ} (o : Obj b N (spMap β)) (π : End0 (av o)) : Prop :=
  ∃ (m d : ℕ) (ψ ψ' : End (av o)), m.Coprime p ∧ d.Coprime p ∧ (m : ℤ) • π = toEnd0 _ ψ ∧
    ψ ≫ ψ' = d • 𝟙 _ ∧ ψ' ≫ ψ = d • 𝟙 _

def FixBridgeC : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (G : HTGroup p) (L : Link D G) (R : Type) [CommRing R] (b : Base D R)
    (β : R →+* ℂ) (N N' : ℕ), 3 ≤ N → N ∣ N' → N'.Coprime p → ∀ (g : G.GAf),
    (∀ k ∈ L.KN N', g * k * g⁻¹ ∈ L.KN N) →
    ∀ (M : Model b N) (M' : Model b N') (q₁ q₂ : M'.X ⟶ M.X), IsHecke L β M' M q₁ 1 → IsHecke L β M' M q₂ g →
    ∀ (y : Sp ℂ ⟶ M'.X) (o : Obj b N' (spMap β)), Classifies M' y o →
      (y ≫ q₂ = y ≫ q₁ ↔ ∃ π ga, PrimeToP o π ∧ IsGamma L o π ga⁻¹ ∧ ga * g⁻¹ ∈ L.KN N) ∧
      ∀ (π : End0 (av o)) ga (π' : End0 (av o)) ga', PrimeToP o π → IsGamma L o π ga⁻¹ → ga * g⁻¹ ∈ L.KN N → PrimeToP o π' → IsGamma L o π' ga'⁻¹ → ga' * g⁻¹ ∈ L.KN N → π = π'

end GlobalTheory.LKCx
