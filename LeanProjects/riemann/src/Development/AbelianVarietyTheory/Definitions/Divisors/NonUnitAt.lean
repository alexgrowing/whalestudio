import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsThetaCompact

noncomputable section

open AlgebraicGeometry CategoryTheory Limits IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH

namespace GlobalTheory.Poinc

structure ATrait (X : Scheme.{0}) where
  V : Type
  [ring : CommRing V]
  [dom : IsDomain V]
  [dvr : IsDiscreteValuationRing V]
  [char : CharZero V]
  complete : IsAdicComplete (maximalIdeal V) V
  ϖ : V
  irr : Irreducible ϖ
  ξ : Sp V ⟶ X

attribute [instance] ATrait.ring ATrait.dom ATrait.dvr ATrait.char

def ATrait.GenIn {X : Scheme.{0}} (T : ATrait X) (U : Set X) : Prop := Set.range (jK T.V ≫ T.ξ) ⊆ U

def ATrait.HasOrd {X : Scheme.{0}} (T : ATrait X) {x : X} (h : T.ξ (closedPoint T.V) ⤳ x) (f : X.presheaf.stalk x)
    (a : ℕ) : Prop :=
  Ideal.span {(Scheme.stalkClosedPointTo T.ξ).hom ((X.presheaf.stalkSpecializes h).hom f)} = Ideal.span {T.ϖ ^ a}

def ATrait.CentredAt {X : Scheme.{0}} (T : ATrait X) (η : X) (e : ℕ) : Prop :=
  T.ξ (closedPoint T.V) = η ∧ Function.Injective (Scheme.stalkClosedPointTo T.ξ).hom ∧ 1 ≤ e ∧
    ∃ h : T.ξ (closedPoint T.V) ⤳ η, (maximalIdeal (X.presheaf.stalk η)).map
      ((Scheme.stalkClosedPointTo T.ξ).hom.comp (X.presheaf.stalkSpecializes h).hom) = Ideal.span {T.ϖ ^ e}

def EqAt {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] (M : RatModel o Ω) (D : EffCartierData M.Z) (x : M.Z) (f : Ω) :
    Prop := ∃ i, x ∈ D.U i ∧ f = valF M.pt (D.U i) (D.f i)

def NonUnitAt {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] (M : RatModel o Ω) (z : M.Z) (h : Ω) : Prop :=
  h ∈ M.O z ∧ (h = 0 ∨ h⁻¹ ∉ M.O z)

end GlobalTheory.Poinc
