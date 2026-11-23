import Mathlib

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar

open AlgebraicGeometry CategoryTheory

variable {X : Scheme.{0}} {Ω : Type} [Field Ω]

def genPt (ξ : Spec (CommRingCat.of Ω) ⟶ X) : X := ξ (IsLocalRing.closedPoint Ω)

def Cpt (ξ : Spec (CommRingCat.of Ω) ⟶ X) : Type := {p : X // genPt ξ ⤳ p}

def genMap (ξ : Spec (CommRingCat.of Ω) ⟶ X) (p : Cpt ξ) : X.presheaf.stalk p.1 →+* Ω :=
  (X.presheaf.stalkSpecializes p.2 ≫ Scheme.stalkClosedPointTo ξ).hom

def regAt (ξ : Spec (CommRingCat.of Ω) ⟶ X) (p : Cpt ξ) : Subring Ω := (genMap ξ p).range

def unitAt (ξ : Spec (CommRingCat.of Ω) ⟶ X) (p : Cpt ξ) (a : Ω) : Prop :=
  a ≠ 0 ∧ a ∈ regAt ξ p ∧ a⁻¹ ∈ regAt ξ p

structure IsCptGen (ξ : Spec (CommRingCat.of Ω) ⟶ X) : Prop where
  bij : Function.Bijective (Scheme.stalkClosedPointTo ξ).hom
  inj : ∀ p : Cpt ξ, Function.Injective (genMap ξ p)

end GlobalTheory.CompanionTheory.Ar
