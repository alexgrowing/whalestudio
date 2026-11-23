import Development.EtaleCohomology.EtaleSheaves.NeighbourhoodKilling

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.E.Bridge_yfiPf
open LateralTheory.E.E4 LateralTheory.E.LeafGhostCut LateralTheory.E.EtaleTopologySheaves LateralTheory.E.LeafDegCut LateralTheory.E.SecondDegreeKilling.Nbhd
  LateralTheory.E.NeighbourhoodKilling LateralTheory.E.SecondDegreeKilling

structure Sys (q : ℕ) (i : ℤ) {B W Y : Scheme.{0}} (p : Y ⟶ B) (ι : W ⟶ B) (U : B.Etale) (m : ℤ) (u : U.left) where
  J : Type
  [cat : SmallCategory J]
  [filt : IsFiltered J]
  V : J → B.Etale
  a : ∀ j, V j ⟶ U
  mem : ∀ j, u ∈ Set.range (a j).left
  tr : ∀ {j k : J}, (j ⟶ k) → (V k ⟶ V j)
  tr_id : ∀ j, tr (𝟙 j) = 𝟙 (V j)
  tr_comp : ∀ {j k l : J} (f : j ⟶ k) (g : k ⟶ l), tr (f ≫ g) = tr g ≫ tr f
  tr_a : ∀ {j k : J} (f : j ⟶ k), tr f ≫ a j = a k
  A : Type
  [ring : CommRing A]
  sh : SH A
  t : Sp A ⟶ U.left
  gY : ∀ j, pullback p (t ≫ U.hom) ⟶ YU p (V j)
  gW : ∀ j, pullback (pullback.snd p (t ≫ U.hom) ≫ (t ≫ U.hom)) ι ⟶ pullback (pullback.snd p (V j).hom ≫ (V j).hom) ι
  sq : ∀ j, prS p ι (t ≫ U.hom) ≫ gY j = gW j ≫ prU p ι (V j)
  gY_a : ∀ j, gY j ≫ resY p (a j) = tY p U t
  gW_a : ∀ j, gW j ≫ resYW p ι (a j) = tW p ι U t
  gY_tr : ∀ {j k : J} (f : j ⟶ k), gY k ≫ resY p (tr f) = gY j
  gW_tr : ∀ {j k : J} (f : j ⟶ k), gW k ≫ resYW p ι (tr f) = gW j
  injY : ∀ j (y : Ht q (sch.obj (YU p (V j))) m i), pull (ZMod q) (sch.map (gY j)) (tw q i) m y = 0 →
    ∃ (k : J) (f : j ⟶ k), pull (ZMod q) (sch.map (resY p (tr f))) (tw q i) m y = 0
  surY : ∀ y : Ht q (sch.obj (pullback p (t ≫ U.hom))) (m - 1) i,
    ∃ (j : J) (y' : Ht q (sch.obj (YU p (V j))) (m - 1) i), pull (ZMod q) (sch.map (gY j)) (tw q i) (m - 1) y' = y
  injW : ∀ j (w : Ht q (sch.obj (pullback (pullback.snd p (V j).hom ≫ (V j).hom) ι)) (m - 1) i),
    pull (ZMod q) (sch.map (gW j)) (tw q i) (m - 1) w = 0 →
    ∃ (k : J) (f : j ⟶ k), pull (ZMod q) (sch.map (resYW p ι (tr f))) (tw q i) (m - 1) w = 0

def Geo : Prop := Hyps → ∀ (q : ℕ) [NeZero q] (k : Type) [Field k], IsUnit (q : k) → ∀ (i : ℤ)
  {B W Y : Scheme.{0}} (_ : B ⟶ Sp k) (ι : W ⟶ B) [IsClosedImmersion ι] (p : Y ⟶ B), IsProper p →
  ∀ (U : B.Etale) (m : ℤ) (u : U.left), Nonempty (Sys q i p ι U m u)

def Pack : Prop := ∀ (q : ℕ) [NeZero q] (i : ℤ) {B W Y : Scheme.{0}} (p : Y ⟶ B) (ι : W ⟶ B) (U : B.Etale) (m : ℤ)
  (u : U.left) (_ : Sys q i p ι U m u) (z : Hrel (ZMod q) (sch.map (prU p ι U)) (tw q i) m),
  ∃ (J : Type) (_ : SmallCategory J) (_ : IsFiltered J) (T : Tri J) (j0 : J) (x0 : T.Rm.obj j0) (A : Type) (_ : CommRing A)
    (t : Sp A ⟶ U.left), SH A ∧
    (LateralTheory.E.SecondDegreeKilling.rT q i p ι U t m z = 0 → (T.cR.ι.app j0).hom x0 = 0) ∧
    ∀ (j : J) (f : j0 ⟶ j), (T.Rm.map f).hom x0 = 0 →
      ∃ (U' : B.Etale) (a : U' ⟶ U), u ∈ Set.range a.left ∧ rY q i p ι a m z = 0

theorem Bridge_of_geo_pack (hG : Geo) (hP : Pack) : Bridge := by
  intro hH q _ k _ hq i B W Y toK ι _ p hp U m z u
  obtain ⟨S⟩ := hG hH q k hq i toK ι p hp U m u
  exact hP q i p ι U m u S z

end LateralTheory.E.Bridge_yfiPf
