import Development.EtaleCohomology.EtaleSheaves.LeafDescCut

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC LateralTheory.E.E4

namespace LateralTheory.E.LeafLocStalkPf

def RelZS (R : Type) [CommRing R] (F : Shv R) (n : ℤ) {U E : Spc} (u : U ⟶ E) : Prop :=
  (∀ m : ℤ, m + 1 = n → Function.Surjective (pull R u F m)) ∧ Function.Injective (pull R u F n)

def StalkH (q : ℕ) [NeZero q] {Y X : Scheme.{0}} (f : Y ⟶ X) (i : ℤ) : Prop :=
  ∀ (A : Type) [CommRing A] (s : Sp A ⟶ X), SH A → IsUnit (q : A) →
    Eqv _ (pullback.snd (cechAug f) (sch.map s)) (tw q i)

def QAll (q : ℕ) [NeZero q] (n : ℤ) : Prop :=
  ∀ {Y X : Scheme.{0}} (f : Y ⟶ X) [IsProper f], IsUnit (q : Γ(X, ⊤)) → ∀ i : ℤ, StalkH q f i →
    RelZS (ZMod q) (tw q i) n (cechAug f)

def LocSurj : Prop := Hyps → ∀ (q : ℕ) [NeZero q] (n : ℤ), (∀ m < n, QAll q m) →
  ∀ {Y X : Scheme.{0}} (f : Y ⟶ X) [IsProper f], IsUnit (q : Γ(X, ⊤)) → ∀ i : ℤ, StalkH q f i →
    ∀ m : ℤ, m + 1 = n → Function.Surjective (pull (ZMod q) (cechAug f) (tw q i) m)

def LocInj : Prop := Hyps → ∀ (q : ℕ) [NeZero q] (n : ℤ), (∀ m < n, QAll q m) →
  ∀ {Y X : Scheme.{0}} (f : Y ⟶ X) [IsProper f], IsUnit (q : Γ(X, ⊤)) → ∀ i : ℤ, StalkH q f i →
    Function.Injective (pull (ZMod q) (cechAug f) (tw q i) n)

def LeafLocStalk : Prop := Hyps → ∀ (q : ℕ) [NeZero q] {Y X : Scheme.{0}} (f : Y ⟶ X) [IsProper f], IsUnit (q : Γ(X, ⊤)) →
  ∀ i : ℤ, (∀ (A : Type) [CommRing A] (s : Sp A ⟶ X), SH A → IsUnit (q : A) →
    Eqv _ (pullback.snd (cechAug f) (sch.map s)) (tw q i)) → Eqv _ (cechAug f) (tw q i)

end LateralTheory.E.LeafLocStalkPf
