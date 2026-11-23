import Development.EtaleCohomology.EtaleSheaves.LeafDegCut

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.E.SecondDegreeKilling
open LateralTheory.E.E4 LateralTheory.E.LeafGhostCut LateralTheory.E.EtaleTopologySheaves LateralTheory.E.LeafDegCut

abbrev prS {Y B W S : Scheme.{0}} (p : Y ⟶ B) (ι : W ⟶ B) (s : S ⟶ B) :
    pullback (pullback.snd p s ≫ s) ι ⟶ pullback p s := pullback.fst _ _

abbrev tY {Y B S : Scheme.{0}} (p : Y ⟶ B) (U : B.Etale) (t : S ⟶ U.left) : pullback p (t ≫ U.hom) ⟶ YU p U :=
  pullback.map p (t ≫ U.hom) p U.hom (𝟙 Y) t (𝟙 B) (by simp) (by simp)

abbrev tW {Y B W S : Scheme.{0}} (p : Y ⟶ B) (ι : W ⟶ B) (U : B.Etale) (t : S ⟶ U.left) :
    pullback (pullback.snd p (t ≫ U.hom) ≫ (t ≫ U.hom)) ι ⟶ pullback (pullback.snd p U.hom ≫ U.hom) ι :=
  pullback.map _ _ _ _ (tY p U t) (𝟙 W) (𝟙 B) (by simp only [tY, pullback.lift_snd_assoc, Category.assoc]; erw [Category.comp_id]) (by simp)

abbrev rT (q : ℕ) (i : ℤ) {Y B W S : Scheme.{0}} (p : Y ⟶ B) (ι : W ⟶ B) (U : B.Etale) (t : S ⟶ U.left) (m : ℤ) :=
  rpl q i (prU p ι U) (prS p ι (t ≫ U.hom)) (tW p ι U t) (tY p U t) (pullback.lift_fst _ _ _).symm m

def LeafKillPt : Prop := Hyps → ∀ (q : ℕ) [NeZero q] (k : Type) [Field k], IsUnit (q : k) → ∀ (i : ℤ)
  {B W Y : Scheme.{0}} (_ : B ⟶ Sp k) (ι : W ⟶ B) [IsClosedImmersion ι] (p : Y ⟶ B), IsProper p →
  ∀ (U : B.Etale) (m : ℤ) (z : Hrel (ZMod q) (sch.map (prU p ι U)) (tw q i) m),
  (∀ (A : Type) [CommRing A] (t : Sp A ⟶ U.left), SH A → rT q i p ι U t m z = 0) →
  Cov U (fun _ a => rY q i p ι a m z = 0)

def LeafPtW : Prop := Hyps → ∀ (q : ℕ) [NeZero q] (k : Type) [Field k], IsUnit (q : k) → ∀ (i : ℤ)
  {B W Y : Scheme.{0}} (_ : B ⟶ Sp k) (ι : W ⟶ B) [IsClosedImmersion ι] (V : B.Opens), (V : Set B) = (Set.range ι)ᶜ →
  ∀ (p : Y ⟶ B), IsProper p → ∀ (A : Type) [CommRing A] (s : Sp A ⟶ B), SH A → ¬ (Set.range s ⊆ V) →
  ∀ m, Subsingleton (Hrel (ZMod q) (sch.map (prS p ι s)) (tw q i) m)

def LeafPtV : Prop := Hyps → ∀ (q : ℕ) [NeZero q] (k : Type) [Field k], IsUnit (q : k) → ∀ (i : ℤ)
  {B W Y Y' : Scheme.{0}} (_ : B ⟶ Sp k) (ι : W ⟶ B) [IsClosedImmersion ι] (V : B.Opens), (V : Set B) = (Set.range ι)ᶜ →
  ∀ (p : Y ⟶ B) (g : Y' ⟶ Y), IsProper p → IsProper (g ≫ p) → ∀ (U : B.Etale) (A : Type) [CommRing A]
  (t : Sp A ⟶ U.left), SH A → Set.range ⇑(t ≫ U.hom) ⊆ (V : Set B) → ∀ (m : ℤ), pl q i (fibMap g p (t ≫ U.hom)) m = 0 →
  ∀ y : Hrel (ZMod q) (sch.map (prU p ι U)) (tw q i) m, rT q i (g ≫ p) ι U t m (gY q i p g ι U m y) = 0

theorem LeafKill2_of (hPt : LeafKillPt) (hW : LeafPtW) (hV : LeafPtV) : LeafKill2 := by
  intro hH q _ k _ hq i B W Y0 Y1 Y2 toK ι _ V hVW p g1 g2 hp hp1 hp2 hS U y
  refine hPt hH q k hq i toK ι (g1 ≫ p) hp1 U 2 _ ?_
  intro A _ t hA
  by_cases hc : Set.range ⇑(t ≫ U.hom) ⊆ (V : Set B)
  · exact hV hH q k hq i toK ι V hVW p g1 hp hp1 U A t hA hc 2 (hS A (t ≫ U.hom) hA hc).2.1 y
  · have := hW hH q k hq i toK ι V hVW (g1 ≫ p) hp1 A (t ≫ U.hom) hA hc 2
    exact Subsingleton.elim _ _

end LateralTheory.E.SecondDegreeKilling
