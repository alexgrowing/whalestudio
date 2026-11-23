import Development.EtaleCohomology.EtaleSheaves.LeafKill1Of
import Development.EtaleCohomology.EtaleSheaves.SecondDegreeKilling.LeafKill2Of

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.E.LeafKill1V2Cut
open LateralTheory.E.E4 LateralTheory.E.LeafGhostCut LateralTheory.E.EtaleTopologySheaves LateralTheory.E.LeafDegCut

abbrev phY {Y B : Scheme.{0}} (p : Y ⟶ B) (U : B.Etale) {A : Type} [CommRing A] (t : Sp A ⟶ U.left) :
    pullback p (t ≫ U.hom) ⟶ LateralTheory.E.LeafKill1Pf.YA p U t :=
  pullback.lift (LateralTheory.E.SecondDegreeKilling.tY p U t) (pullback.snd p (t ≫ U.hom))
    (pullback.lift_snd _ _ _)

abbrev phW {Y B W : Scheme.{0}} (p : Y ⟶ B) (ι : W ⟶ B) (U : B.Etale) {A : Type} [CommRing A] (t : Sp A ⟶ U.left) :
    pullback (pullback.snd p (t ≫ U.hom) ≫ (t ≫ U.hom)) ι ⟶ pullback (pullback.snd (toBY p U) t ≫ t ≫ U.hom) ι :=
  pullback.map _ _ _ _ (phY p U t) (𝟙 W) (𝟙 B)
    (by erw [Category.comp_id, pullback.lift_snd_assoc]) (by simp)

theorem rT_eq_zero_of_ptA (q : ℕ) (i : ℤ) {Y B W : Scheme.{0}} (p : Y ⟶ B) (ι : W ⟶ B) (U : B.Etale) {A : Type}
    [CommRing A] (t : Sp A ⟶ U.left) (m : ℤ) (y : Hrel (ZMod q) (sch.map (prU p ι U)) (tw q i) m)
    (h : LateralTheory.E.LeafKill1Pf.ptA q i p ι U t m y = 0) : LateralTheory.E.SecondDegreeKilling.rT q i p ι U t m y = 0 := by
  have c1 : LateralTheory.E.SecondDegreeKilling.prS p ι (t ≫ U.hom) ≫ phY p U t = phW p ι U t ≫ LateralTheory.E.LeafKill1Pf.prA p ι U t :=
    (pullback.lift_fst _ _ _).symm
  have hY : phY p U t ≫ pullback.fst (toBY p U) t = LateralTheory.E.SecondDegreeKilling.tY p U t := pullback.lift_fst _ _ _
  have hW : phW p ι U t ≫ LateralTheory.E.LeafKill1Pf.aW p ι U t = LateralTheory.E.SecondDegreeKilling.tW p ι U t := by
    apply pullback.hom_ext
    · simp only [Category.assoc, LateralTheory.E.LeafKill1Pf.aW, LateralTheory.E.SecondDegreeKilling.tW, phW, pullback.lift_fst,
        pullback.lift_fst_assoc]
    · simp only [Category.assoc, LateralTheory.E.LeafKill1Pf.aW, LateralTheory.E.SecondDegreeKilling.tW, phW, pullback.lift_snd, Category.comp_id]
  have key := LateralTheory.E.SecondDegreeKilling.Comp.rpl_comp q i (prU p ι U) (LateralTheory.E.LeafKill1Pf.prA p ι U t)
    (LateralTheory.E.SecondDegreeKilling.prS p ι (t ≫ U.hom)) (LateralTheory.E.LeafKill1Pf.aW p ι U t) (pullback.fst (toBY p U) t)
    (pullback.lift_fst _ _ _).symm (phW p ι U t) (phY p U t) c1
    (by rw [hY, hW]; exact (pullback.lift_fst _ _ _).symm) m y
  rw [LateralTheory.E.SecondDegreeKilling.Nbhd.rpl_congr q i _ _ _ _ _ _ _ (pullback.lift_fst _ _ _).symm hW hY m] at key
  show LateralTheory.E.SecondDegreeKilling.rT q i p ι U t m y = 0
  rw [LateralTheory.E.SecondDegreeKilling.rT, ← key]
  erw [h, map_zero]

theorem goal_of (hN : LateralTheory.E.SecondDegreeKilling.Nbhd.LeafKillNbhd) (hW : LateralTheory.E.SecondDegreeKilling.LeafPtW)
    (hV : LateralTheory.E.LeafKill1Pf.LeafPtV) : LateralTheory.E.LeafDegCut.LeafKill1 := by
  intro hH q _ k _ hq i B W Y0 Y1 Y2 s ι _ V hV' p g1 g2 hp hp1 hp2 hSHV U y
  refine LateralTheory.E.SecondDegreeKilling.Nbhd.killPt_of hN hH q k hq i s ι (g2 ≫ g1 ≫ p) hp2 U 1 (gY q i (g1 ≫ p) g2 ι U 1 y) ?_
  intro A _ t hA
  by_cases h : Set.range (t ≫ U.hom : Sp A ⟶ B) ⊆ (V : Set B)
  · exact rT_eq_zero_of_ptA q i (g2 ≫ g1 ≫ p) ι U t 1 _ (hV hH q k hq i s ι V hV' p g1 g2 hp hp1 hp2 hSHV U y A t hA h)
  · have := hW hH q k hq i s ι V hV' (g2 ≫ g1 ≫ p) hp2 A (t ≫ U.hom) hA h 1
    exact Subsingleton.elim _ _

theorem goal_of' (hN : LateralTheory.E.SecondDegreeKilling.Nbhd.LeafKillNbhd) (hW : LateralTheory.E.SecondDegreeKilling.LeafPtW)
    (hV : LateralTheory.E.SecondDegreeKilling.LeafPtV) : LateralTheory.E.LeafDegCut.LeafKill1 := by
  intro hH q _ k _ hq i B W Y0 Y1 Y2 s ι _ V hV' p g1 g2 hp hp1 hp2 hSHV U y
  refine LateralTheory.E.SecondDegreeKilling.Nbhd.killPt_of hN hH q k hq i s ι (g2 ≫ g1 ≫ p) hp2 U 1 (gY q i (g1 ≫ p) g2 ι U 1 y) ?_
  intro A _ t hA
  by_cases h : Set.range (t ≫ U.hom : Sp A ⟶ B) ⊆ (V : Set B)
  · exact hV hH q k hq i s ι V hV' (g1 ≫ p) g2 hp1 hp2 U A t hA h 1 (hSHV A (t ≫ U.hom) hA h).2.2.1 y
  · have := hW hH q k hq i s ι V hV' (g2 ≫ g1 ≫ p) hp2 A (t ≫ U.hom) hA h 1
    exact Subsingleton.elim _ _

end LateralTheory.E.LeafKill1V2Cut
