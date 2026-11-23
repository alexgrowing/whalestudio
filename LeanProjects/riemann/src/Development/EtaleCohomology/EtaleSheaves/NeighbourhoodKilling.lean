import Development.EtaleCohomology.EtaleSheaves.SecondDegreeKilling.LeafKill2Of
import Development.EtaleCohomology.EtaleSheaves.GlueRelPf

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.E.NeighbourhoodKilling
open LateralTheory.E.E4 LateralTheory.E.LeafGhostCut LateralTheory.E.EtaleTopologySheaves LateralTheory.E.LeafDegCut LateralTheory.E.SecondDegreeKilling.Nbhd

structure Tri (J : Type) [SmallCategory J] where
  Rm : J ⥤ AddCommGrpCat.{1}
  Ym : J ⥤ AddCommGrpCat.{1}
  Yp : J ⥤ AddCommGrpCat.{1}
  Wp : J ⥤ AddCommGrpCat.{1}
  cR : Cocone Rm
  cYm : Cocone Ym
  cYp : Cocone Yp
  cWp : Cocone Wp
  fg : Rm ⟶ Ym
  fgL : cR.pt ⟶ cYm.pt
  fg_w : ∀ j, cR.ι.app j ≫ fgL = fg.app j ≫ cYm.ι.app j
  dl : Wp ⟶ Rm
  dlL : cWp.pt ⟶ cR.pt
  dl_w : ∀ j, cWp.ι.app j ≫ dlL = dl.app j ≫ cR.ι.app j
  rs : Yp ⟶ Wp
  rsL : cYp.pt ⟶ cWp.pt
  rs_w : ∀ j, cYp.ι.app j ≫ rsL = rs.app j ≫ cWp.ι.app j

  exR : ∀ j (x : Rm.obj j), (fg.app j).hom x = 0 → ∃ w, (dl.app j).hom w = x

  exWL : ∀ w : cWp.pt, dlL.hom w = 0 → ∃ y, rsL.hom y = w

  cx : ∀ j (y : Yp.obj j), (dl.app j).hom ((rs.app j).hom y) = 0

  injYm : ∀ j (y : Ym.obj j), (cYm.ι.app j).hom y = 0 → ∃ (k : J) (f : j ⟶ k), (Ym.map f).hom y = 0

  surYp : ∀ y : cYp.pt, ∃ (j : J) (y' : Yp.obj j), (cYp.ι.app j).hom y' = y

  injWp : ∀ j (w : Wp.obj j), (cWp.ι.app j).hom w = 0 → ∃ (k : J) (f : j ⟶ k), (Wp.map f).hom w = 0

def PairFive : Prop := ∀ (J : Type) [SmallCategory J] [IsFiltered J] (T : Tri J) (j : J) (x : T.Rm.obj j),
  (T.cR.ι.app j).hom x = 0 → ∃ (k : J) (f : j ⟶ k), (T.Rm.map f).hom x = 0

def ObsExact : Prop := ∀ (q : ℕ) [NeZero q] {U E : Spc} (u : U ⟶ E) (i m : ℤ) (y : Hrel (ZMod q) u (tw q i) (m + 1)),
  fgt (ZMod q) u (tw q i) (m + 1) y = 0 → ∃ w, LateralTheory.E.GlueRelPf.obs q u i m w = y

def ObsNat : Prop := ∀ (q : ℕ) [NeZero q] {U E U' E' : Spc} (f : U ⟶ E) (f' : U' ⟶ E') (u : U' ⟶ U) (e : E' ⟶ E)
  (comm : f' ≫ e = u ≫ f) (i m : ℤ) (w : Ht q U m i),
  rpull (ZMod q) f f' u e comm (tw q i) (m + 1) (LateralTheory.E.GlueRelPf.obs q f i m w) =
    LateralTheory.E.GlueRelPf.obs q f' i m (pull (ZMod q) u (tw q i) m w)

def Bridge : Prop := Hyps → ∀ (q : ℕ) [NeZero q] (k : Type) [Field k], IsUnit (q : k) → ∀ (i : ℤ)
  {B W Y : Scheme.{0}} (_ : B ⟶ Sp k) (ι : W ⟶ B) [IsClosedImmersion ι] (p : Y ⟶ B), IsProper p →
  ∀ (U : B.Etale) (m : ℤ) (z : Hrel (ZMod q) (sch.map (prU p ι U)) (tw q i) m) (u : U.left),
  ∃ (J : Type) (_ : SmallCategory J) (_ : IsFiltered J) (T : Tri J) (j0 : J) (x0 : T.Rm.obj j0) (A : Type) (_ : CommRing A)
    (t : Sp A ⟶ U.left), SH A ∧
    (LateralTheory.E.SecondDegreeKilling.rT q i p ι U t m z = 0 → (T.cR.ι.app j0).hom x0 = 0) ∧
    ∀ (j : J) (f : j0 ⟶ j), (T.Rm.map f).hom x0 = 0 →
      ∃ (U' : B.Etale) (a : U' ⟶ U), u ∈ Set.range a.left ∧ rY q i p ι a m z = 0

theorem goal_of (hF : PairFive) (_hO : ObsExact) (_hN : ObsNat) (hB : Bridge) : LeafKillNbhd := by
  intro hH q _ k _ hq i B W Y toK ι _ p hp U m z hz u
  obtain ⟨J, _, _, T, j0, x0, A, _, t, hSH, hlim, hst⟩ := hB hH q k hq i toK ι p hp U m z u
  obtain ⟨j, f, hf⟩ := hF J T j0 x0 (hlim (hz A t hSH))
  exact hst j f hf

end LateralTheory.E.NeighbourhoodKilling
