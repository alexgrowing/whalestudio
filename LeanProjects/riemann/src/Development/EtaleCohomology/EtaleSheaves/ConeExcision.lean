import Development.EtaleCohomology.EtaleSheaves.LeafChartRing

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex GlobalTheory.EtC LateralTheory.E.t_E6Cut

namespace LateralTheory.E.LeafExcPf

def LeafMono : Prop := ∀ (R : Type) [CommRing R] {E E' : Spc} (f : E ⟶ E') [Mono f] (n : ℤ),
  Mono (((chains R).map f).f n)

def LeafSq : Prop := ∀ (R : Type) [CommRing R] {U E' E : Spc} (f : U ⟶ E) [Mono f] (g : E' ⟶ E),
  (∀ (p : ℕ) (T : Scheme.{0}) (y : Sx E p T), EtLoc T fun V k =>
    (∃ u : Sx U p V, sxMap f u = sxRes k y) ∨ ∃ a : Sx E' p V, sxMap g a = sxRes k y) →
  (∀ (p : ℕ) (T : Scheme.{0}) (a b : Sx E' p T), sxMap g a = sxMap g b → EtLoc T fun V k =>
    sxRes k a = sxRes k b ∨ ∃ u : Sx U p V, sxMap f u = sxRes k (sxMap g a)) →
  ∀ n : ℤ, IsPushout (((chains R).map (pullback.snd f g)).f n) (((chains R).map (pullback.fst f g)).f n)
    (((chains R).map g).f n) (((chains R).map f).f n)

def LeafConePush : Prop := A1 → ∀ (R : Type) [CommRing R] (F : Shv R) {K' L' K L : Cx R}
  (a : K' ⟶ L') (u : K' ⟶ K) (v : L' ⟶ L) (b : K ⟶ L), a ≫ v = u ≫ b →
  (∀ n, Mono (a.f n)) → (∀ n, Mono (b.f n)) → (∀ n, IsPushout (a.f n) (u.f n) (v.f n) (b.f n)) →
  ∀ n : ℤ, (Subsingleton (HK R (mappingCone a) F n) ↔ Subsingleton (HK R (mappingCone b) F n))

theorem LeafExc_of (hRel : LeafRel) (hMono : LeafMono) (hSq : LeafSq) (hCone : LeafConePush) : LeafExc := by
  intro hA1 R _ F c U E' E f _ g h1 h2
  unfold Conn
  rw [hRel R F c, hRel R F c]
  have hsq : (chains R).map (pullback.snd f g) ≫ (chains R).map g =
      (chains R).map (pullback.fst f g) ≫ (chains R).map f := by
    rw [← Functor.map_comp, ← Functor.map_comp, pullback.condition]
  have key := hCone hA1 R F _ _ _ _ hsq (fun n => hMono R _ n) (fun n => hMono R f n) (hSq R f g h1 h2)
  constructor
  · intro h n hn; exact (key n).2 (h n hn)
  · intro h n hn; exact (key n).1 (h n hn)

end LateralTheory.E.LeafExcPf
