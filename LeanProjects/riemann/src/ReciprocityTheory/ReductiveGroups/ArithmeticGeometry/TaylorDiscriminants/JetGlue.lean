import Mathlib

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory

namespace ReciprocityTheory.ChartRestriction.G.TB

abbrev JetRing (S : Type) [CommRing S] (κ : Type) (m : ℕ) : Type :=
  MvPolynomial κ S ⧸ (Ideal.span (Set.range (MvPolynomial.X : κ → MvPolynomial κ S))) ^ (m + 1)

abbrev JetLoc (S : Type) [CommRing S] (κ : Type) (m : ℕ) (𝔭 : Ideal S) [𝔭.IsPrime] : Type :=
  Localization (Algebra.algebraMapSubmonoid (JetRing S κ m) 𝔭.primeCompl)

def JetGlueSt : Prop :=
  ∀ (S : Type) [CommRing S] (κ : Type) [Finite κ] (m : ℕ) (X : Scheme.{0})
    (f g : Spec (CommRingCat.of (JetRing S κ m)) ⟶ X),
    (∀ (𝔭 : Ideal S) [𝔭.IsPrime],
      Spec.map (CommRingCat.ofHom (algebraMap (JetRing S κ m) (JetLoc S κ m 𝔭))) ≫ f =
        Spec.map (CommRingCat.ofHom (algebraMap (JetRing S κ m) (JetLoc S κ m 𝔭))) ≫ g) →
    f = g

end ReciprocityTheory.ChartRestriction.G.TB
