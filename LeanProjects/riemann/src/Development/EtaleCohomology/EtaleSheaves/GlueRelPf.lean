import Development.EtaleCohomology.EtaleSheaves.LocGlueEtPf

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC LateralTheory.E.E4 LateralTheory.E.LeafLocStalkPf LateralTheory.E.LocSurjPf
  LateralTheory.E.LocGlueEtPf CochainComplex.HomComplex

namespace LateralTheory.E.GlueRelPf

def obs (q : ℕ) [NeZero q] {U E : Spc} (u : U ⟶ E) (i m : ℤ) : Ht q U m i →+ Hrel (ZMod q) u (tw q i) (m + 1) :=
  HK.pre (ZMod q) (CochainComplex.mappingCone.fst ((chains (ZMod q)).map u)) (tw q i) m (m + 1) (add_comm 1 m)

def ConeExact : Prop := ∀ (R : Type) [CommRing R] {K L : Cx R} (φ : K ⟶ L) (F : Shv R) (m : ℤ),
  Function.Exact (HK.pull R φ F m) (HK.pre R (CochainComplex.mappingCone.fst φ) F m (m + 1) (add_comm 1 m))

def EdgeInj : Prop := Hyps → ∀ (q : ℕ) [NeZero q] (n i : ℤ) {Y X : Scheme.{0}} (f : Y ⟶ X),
  (∀ (W : Scheme.{0}) (w : W ⟶ X), Etale w → ∀ m' < n, RelZS (ZMod q) (tw q i) m' (cechAug (pullback.snd f w))) →
  ∀ (V : Scheme.{0}) (v : V ⟶ X), Etale v → Surjective v → ∀ m : ℤ, m + 1 = n → ∀ y : Ht q (cech f) m i,
    obs q (cechAug (pullback.snd f v)) i m (pull (ZMod q) (bcMap f v) (tw q i) m y) = 0 → obs q (cechAug f) i m y = 0

theorem GlueRel_of (hC : ConeExact) (hE : EdgeInj) : GlueRel := by
  intro h q _ n i Y X f hb m hm y hy
  obtain ⟨V, v, hv, hs, z, hz⟩ := hy
  have h1 : obs q (cechAug (pullback.snd f v)) i m (pull (ZMod q) (bcMap f v) (tw q i) m y) = 0 := by
    rw [← hz]
    exact (hC (ZMod q) ((chains (ZMod q)).map (cechAug (pullback.snd f v))) (tw q i) m).apply_apply_eq_zero z
  have h2 := hE h q n i f hb V v hv hs m hm y h1
  exact (hC (ZMod q) ((chains (ZMod q)).map (cechAug f)) (tw q i) m y).1 h2

end LateralTheory.E.GlueRelPf
