import Development.EtaleCohomology.EtaleSheaves.LeafPointTransferCut

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex GlobalTheory.EtC

namespace LateralTheory.E.E8

def LeafArtinAffine : Prop := Base → ∀ (q : ℕ) [NeZero q] (k : Type) [Field k] [IsAlgClosed k], IsUnit (q : k) →
  ∀ {X : Scheme.{0}} (p : X ⟶ Spec (CommRingCat.of k)) [IsProper p] (d : ℕ), DimLE p d →
  ∀ V : X.Opens, IsAffineOpen V → ∀ (n i : ℤ), (d : ℤ) < n → Subsingleton (H (ZMod q) (sch.obj V) (tw q i) n)

def LeafMVVanish : Prop := Base → ∀ (R : Type) [CommRing R] {X : Scheme.{0}} (A B : X.Opens) (F : Shv R) (c : ℤ),
  (∀ n : ℤ, c < n → Subsingleton (H R (sch.obj A) F n)) → (∀ n : ℤ, c < n → Subsingleton (H R (sch.obj B) F n)) →
  (∀ n : ℤ, c - 1 < n → Subsingleton (H R (sch.obj ((A ⊓ B : X.Opens) : Scheme.{0})) F n)) →
  ∀ n : ℤ, c < n → Subsingleton (H R (sch.obj ((A ⊔ B : X.Opens) : Scheme.{0})) F n)

def LeafEmptyVanish : Prop := ∀ (R : Type) [CommRing R] {X : Scheme.{0}} (F : Shv R) (n : ℤ),
  Subsingleton (H R (sch.obj (⊥ : X.Opens)) F n)

end LateralTheory.E.E8

end
