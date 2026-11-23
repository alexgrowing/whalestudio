import Development.EtaleCohomology.EtaleSheaves.LeafLocStalkPf

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC LateralTheory.E.E4 LateralTheory.E.LeafLocStalkPf

namespace LateralTheory.E.LocSurjPf

def bcMap {Y X V : Scheme.{0}} (f : Y ⟶ X) (v : V ⟶ X) : cech (pullback.snd f v) ⟶ cech f :=
  Arrow.mapCechNerve (Arrow.homMk (f := Arrow.mk (yoneda.map (pullback.snd f v))) (g := Arrow.mk (yoneda.map f))
    (yoneda.map (pullback.fst f v)) (yoneda.map v)
    (by simp only [Arrow.mk_hom, ← Functor.map_comp, pullback.condition]))

def EtLift (q : ℕ) [NeZero q] {Y X : Scheme.{0}} (f : Y ⟶ X) (i m : ℤ) (y : Ht q (cech f) m i) : Prop :=
  ∃ (V : Scheme.{0}) (v : V ⟶ X), Etale v ∧ Surjective v ∧
    ∃ z : Ht q (sch.obj V) m i, pull (ZMod q) (cechAug (pullback.snd f v)) (tw q i) m z = pull (ZMod q) (bcMap f v) (tw q i) m y

def LocLiftEt : Prop := Hyps → ∀ (q : ℕ) [NeZero q] (n : ℤ), (∀ m < n, QAll q m) →
  ∀ {Y X : Scheme.{0}} (f : Y ⟶ X) [IsProper f], IsUnit (q : Γ(X, ⊤)) → ∀ i : ℤ, StalkH q f i →
    ∀ m : ℤ, m + 1 = n → ∀ y : Ht q (cech f) m i, EtLift q f i m y

def LocGlueEt : Prop := Hyps → ∀ (q : ℕ) [NeZero q] (n : ℤ), (∀ m < n, QAll q m) →
  ∀ {Y X : Scheme.{0}} (f : Y ⟶ X) [IsProper f], IsUnit (q : Γ(X, ⊤)) → ∀ i : ℤ, StalkH q f i →
    ∀ m : ℤ, m + 1 = n → ∀ y : Ht q (cech f) m i, EtLift q f i m y →
      y ∈ Set.range (pull (ZMod q) (cechAug f) (tw q i) m)

end LateralTheory.E.LocSurjPf
