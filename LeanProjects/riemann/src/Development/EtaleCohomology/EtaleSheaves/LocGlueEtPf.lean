import Development.EtaleCohomology.EtaleSheaves.LocSurjPf

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC LateralTheory.E.E4 LateralTheory.E.LeafLocStalkPf LateralTheory.E.LocSurjPf

namespace LateralTheory.E.LocGlueEtPf

def StalkBC : Prop := Hyps → ∀ (q : ℕ) [NeZero q] {Y X W : Scheme.{0}} (f : Y ⟶ X) (w : W ⟶ X), Etale w → ∀ i : ℤ,
  StalkH q f i → StalkH q (pullback.snd f w) i

def GlueRel : Prop := Hyps → ∀ (q : ℕ) [NeZero q] (n : ℤ) (i : ℤ) {Y X : Scheme.{0}} (f : Y ⟶ X),
  (∀ (W : Scheme.{0}) (w : W ⟶ X), Etale w → ∀ m' < n, RelZS (ZMod q) (tw q i) m' (cechAug (pullback.snd f w))) →
    ∀ m : ℤ, m + 1 = n → ∀ y : Ht q (cech f) m i, EtLift q f i m y →
      y ∈ Set.range (pull (ZMod q) (cechAug f) (tw q i) m)

end LateralTheory.E.LocGlueEtPf
