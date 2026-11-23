import Formalism.LocalToGlobal.Columns.TiedMvG
import Formalism.LocalToGlobal.Columns.TiedMvB
import Formalism.LocalToGlobal.Columns.HermOwed

open NumberField IsDedekindDomain Module Matrix
open scoped TensorProduct

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.UG

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Any

variable {D : ColRec} {u : D.what₂.Word} {A : CF.AtTTied u} {P : ∀ i hi, CF.LvTied u A i hi} (H : CH.HermCols D) (M : AtTMovesC A P)

theorem hxm_adI_up (i : ℕ) (h1 : 1 ≤ i) (hm : i ≤ D.R.m) (v : (D.mem u).A.vT) (c : (D.mem u).C.cls i) (y : ↥(CH.Ld D u i c))
    (h : Formalism.L2.Herm.AdStep D.sp.cm.sig (D.sp.X i).gram (H.lev u i h1 hm).U ((H.cls u i h1 hm).y c)
      ((H.cls u i h1 hm).y ((D.fm u).up i v c ((P i hm).pr v c (hxLd i hm c y))))
      (Formalism.L2.Forms.reGL (CF.rankN D i hm).symm _ (M.upG i hm v c (hxLd i hm c y)).1) (H.vT u v).1) :
    CH.AdI D H u i h1 hm c ((D.fm u).up i v c (hxPr A P i v c y)) (M.toMoves.upG i v c y) v := by
  rw [hxPr_eq A P i hm]
  show Formalism.L2.Herm.AdStep _ _ _ _ _ (Formalism.L2.Herm.toGLb (D.sp.X i).frame (M.upS i v c y).1) _
  rw [M.upS_eq i hm, hxG_toGLb]
  exact h

theorem hxm_adI_dn (i : ℕ) (h1 : 1 ≤ i) (hm : i ≤ D.R.m) (v : (D.mem u).A.vT) (c : (D.mem u).C.cls i)
    (g : Module.Dual ((D.mem u).A.Fv v) ((D.fm u).lk i v c))
    (h : Formalism.L2.Herm.AdStep D.sp.cm.sig (D.sp.X i).gram (H.lev u i h1 hm).U ((H.cls u i h1 hm).y c)
      ((H.cls u i h1 hm).y ((D.fm u).dn i v c g))
      (Formalism.L2.Forms.reGL (CF.rankN D i hm).symm _ (M.dnG i hm v c g).1) (H.vT u v).1) :
    CH.AdI D H u i h1 hm c ((D.fm u).dn i v c g) (M.toMoves.dnG i v c g) v := by
  show Formalism.L2.Herm.AdStep _ _ _ _ _ (Formalism.L2.Herm.toGLb (D.sp.X i).frame (M.dnS i v c g).1) _
  rw [M.dnS_eq i hm, hxG_toGLb]
  exact h

theorem hxm_adI_dil (i : ℕ) (h1 : 1 ≤ i) (hm : i ≤ D.R.m) (v : (D.mem u).A.vT) (a : ((D.mem u).A.Fv v)ˣ) (c : (D.mem u).C.cls i)
    (h : Formalism.L2.Herm.AdStep D.sp.cm.sig (D.sp.X i).gram (H.lev u i h1 hm).U ((H.cls u i h1 hm).y c)
      ((H.cls u i h1 hm).y ((D.fm u).dil i v a c))
      (Formalism.L2.Forms.reGL (CF.rankN D i hm).symm _ (M.dilG i hm v a c).1) (H.vT u v).1) :
    CH.AdI D H u i h1 hm c ((D.fm u).dil i v a c) (M.toMoves.dilG i v a c) v := by
  show Formalism.L2.Herm.AdStep _ _ _ _ _ (Formalism.L2.Herm.toGLb (D.sp.X i).frame (M.dilS i v a c).1) _
  rw [M.dilS_eq i hm, hxG_toGLb]
  exact h

theorem adjacency_level_zero_up (v : (D.mem u).A.vT) (c : (D.mem u).C.cls 0) (y : ↥(CH.Ld D u 0 c))
    (h : Formalism.L2.Herm.AdStep D.sp.cm.sig D.sp.gram0 (H.lev0 u).U ((H.lev0 u).y c)
      ((H.lev0 u).y ((D.fm u).up 0 v c ((P 0 (Nat.zero_le _)).pr v c (hxLd 0 (Nat.zero_le _) c y))))
      (Formalism.L2.Forms.reGL (Formalism.L2.Forms.rank_eq_first_level D.R).symm _ (M.upG 0 (Nat.zero_le _) v c (hxLd 0 (Nat.zero_le _) c y)).1) (H.vT u v).1) :
    CH.Ad0 D H u c ((D.fm u).up 0 v c (hxPr A P 0 v c y)) (M.toMoves.upG 0 v c y) v := by
  rw [hxPr_eq A P 0 (Nat.zero_le _)]
  show Formalism.L2.Herm.AdStep _ _ _ _ _ (Formalism.L2.Herm.toGLb ((D.sp.X 0).frame.reindex (finCongr D.sp.rank0)) (M.upS 0 v c y).1) _
  rw [M.upS_eq 0 (Nat.zero_le _), hxG_toGLb0]
  exact h

theorem adjacency_level_zero_down (v : (D.mem u).A.vT) (c : (D.mem u).C.cls 0) (g : Module.Dual ((D.mem u).A.Fv v) ((D.fm u).lk 0 v c))
    (h : Formalism.L2.Herm.AdStep D.sp.cm.sig D.sp.gram0 (H.lev0 u).U ((H.lev0 u).y c) ((H.lev0 u).y ((D.fm u).dn 0 v c g))
      (Formalism.L2.Forms.reGL (Formalism.L2.Forms.rank_eq_first_level D.R).symm _ (M.dnG 0 (Nat.zero_le _) v c g).1) (H.vT u v).1) :
    CH.Ad0 D H u c ((D.fm u).dn 0 v c g) (M.toMoves.dnG 0 v c g) v := by
  show Formalism.L2.Herm.AdStep _ _ _ _ _ (Formalism.L2.Herm.toGLb ((D.sp.X 0).frame.reindex (finCongr D.sp.rank0)) (M.dnS 0 v c g).1) _
  rw [M.dnS_eq 0 (Nat.zero_le _), hxG_toGLb0]
  exact h

theorem adjacency_level_zero_dilation (v : (D.mem u).A.vT) (a : ((D.mem u).A.Fv v)ˣ) (c : (D.mem u).C.cls 0)
    (h : Formalism.L2.Herm.AdStep D.sp.cm.sig D.sp.gram0 (H.lev0 u).U ((H.lev0 u).y c) ((H.lev0 u).y ((D.fm u).dil 0 v a c))
      (Formalism.L2.Forms.reGL (Formalism.L2.Forms.rank_eq_first_level D.R).symm _ (M.dilG 0 (Nat.zero_le _) v a c).1) (H.vT u v).1) :
    CH.Ad0 D H u c ((D.fm u).dil 0 v a c) (M.toMoves.dilG 0 v a c) v := by
  show Formalism.L2.Herm.AdStep _ _ _ _ _ (Formalism.L2.Herm.toGLb ((D.sp.X 0).frame.reindex (finCongr D.sp.rank0)) (M.dilS 0 v a c).1) _
  rw [M.dilS_eq 0 (Nat.zero_le _), hxG_toGLb0]
  exact h

end Any

section Rec

variable {d : ColDat} (a : ColArgs d) (hS : SpStd d.toColBase) (hH : HostHyp d)

set_option maxHeartbeats 4000000 in

def atTMovesC (u : d.what₂.Word) : AtTMovesC (atTTied a hH u) (fun i hi => levelAgreement a hS hH u i hi) where
  upG := fun i hi v c y => tamG d.sp.cm (stepCrd a hS hH u i hi) (tamMv (Pr := d.Pr) d.W d.lev u i
    ((d.repr u i c).upL v (d.Pr.T u : 𝓞 d.X.E) (tiePr d.sp.cm d.hPr d.σ₀ u (d.repr u i) (stepCrd a hS hH u i hi) v c y)))
  up_tie := fun i hi v c y hy => tam_up (Pr := d.Pr) d.W d.lev d.sp.cm d.hX d.hPr d.σ₀ u i (stepCrd a hS hH u i hi) v c y hy
  dnG := fun i hi v c g => tamG d.sp.cm (stepCrd a hS hH u i hi) (tamMv (Pr := d.Pr) d.W d.lev u i ((d.repr u i c).dnL v g))
  dn_tie := fun i hi v c g hg => tam_dn (Pr := d.Pr) d.W d.lev d.sp.cm d.hX d.hPr d.σ₀ u i (stepCrd a hS hH u i hi) v c g hg
  dilG := fun i hi v x c => tamG d.sp.cm (stepCrd a hS hH u i hi) (tamMv (Pr := d.Pr) d.W d.lev u i ((d.repr u i c).dia1 v x))
  dil_tie := fun i hi v x c => tam_dil (Pr := d.Pr) d.W d.lev d.sp.cm d.hPr d.σ₀ u i (stepCrd a hS hH u i hi) v x c

def atTMoves (u : d.what₂.Word) : AtTMoves (atTTied a hH u) (fun i hi => levelAgreement a hS hH u i hi) :=
  (atTMovesC a hS hH u).toMoves

end Rec

section AdRec

variable {d : ColDat} (a : ColArgs d) (hS : SpStd d.toColBase) (hH : HostHyp d) (hP : PtSurj d) (hK : LocalLevelIsKOneEverywhere d)
  (S : GSplit (Pr := d.Pr) d.sp.cm) (hI : IwAll d S)

theorem th_adI (u : d.what₂.Word) (i : ℕ) (hm : i ≤ d.R.m) (v : d.Pr.vT u) (c : StCl (Pr := d.Pr) d.W d.lev u i)
    (d₁ : DecoSet d.X.E (d.R.N i) (d.Pr.vT u) d.Pr.vGs)
    (h : Deco.SameOff (d.Pr.vT u) d.Pr.vGs (tieEV d.sp.cm d.hX d.hPr u v).1 (d.repr u i c).1 d₁.1) :
    Formalism.L2.Herm.AdStep d.sp.cm.sig (d.sp.X i).gram (hermPack hS hP hK u i hm).lev.U ((hermPack hS hP hK u i hm).cls.y c).1
      ((hermPack hS hP hK u i hm).cls.y (clsD (colVal (Pr := d.Pr) d.W u i (d.Pr.vT u) d.Pr.vGs) (d.lev i) d₁)).1
      (Formalism.L2.Forms.reGL (d.sp.X_rank i hm).symm _ (ufGL d.X.E (d.R.N i) (tamMv (Pr := d.Pr) d.W d.lev u i d₁)))
      (tieEV d.sp.cm d.hX d.hPr u v).1 :=
  tam_ad d.sp.cm d.hX d.hPr d.σ₀ u (d.lev i) (colDia (X := d.X) (Pr := d.Pr) d.R u i) (d.repr u i) (hP u i)
    (fun c => (stepGSD (Pr := d.Pr) d.W d.lev u i).outSec.spec c) (hK u i) (hCrd hS u i hm) _ c _ d₁ h
    ((stepGSD (Pr := d.Pr) d.W d.lev u i).outSec.mv d₁) ((stepGSD (Pr := d.Pr) d.W d.lev u i).outSec.mv_smul d₁)

theorem adjacency_level_zero_tied (u : d.what₂.Word) (v : d.Pr.vT u) (c : StCl (Pr := d.Pr) d.W d.lev u 0)
    (d₁ : DecoSet d.X.E (d.R.N 0) (d.Pr.vT u) d.Pr.vGs)
    (h : Deco.SameOff (d.Pr.vT u) d.Pr.vGs (tieEV d.sp.cm d.hX d.hPr u v).1 (d.repr u 0 c).1 d₁.1) :
    Formalism.L2.Herm.AdStep d.sp.cm.sig d.sp.gram0 (hermPack0 hS hP hK u).lev.U ((hermPack0 hS hP hK u).cls.y c).1
      ((hermPack0 hS hP hK u).cls.y (clsD (colVal (Pr := d.Pr) d.W u 0 (d.Pr.vT u) d.Pr.vGs) (d.lev 0) d₁)).1
      (Formalism.L2.Forms.reGL (Formalism.L2.Forms.rank_eq_first_level d.R).symm _ (ufGL d.X.E (d.R.N 0) (tamMv (Pr := d.Pr) d.W d.lev u 0 d₁)))
      (tieEV d.sp.cm d.hX d.hPr u v).1 :=
  tam_ad d.sp.cm d.hX d.hPr d.σ₀ u (d.lev 0) (colDia (X := d.X) (Pr := d.Pr) d.R u 0) (d.repr u 0) (hP u 0)
    (fun c => (stepGSD (Pr := d.Pr) d.W d.lev u 0).outSec.spec c) (hK u 0) (hCrd0 hS u) _ c _ d₁ h
    ((stepGSD (Pr := d.Pr) d.W d.lev u 0).outSec.mv d₁) ((stepGSD (Pr := d.Pr) d.W d.lev u 0).outSec.mv_smul d₁)

set_option maxHeartbeats 4000000 in

theorem adTied (O : AtTOwed a hS hH) (hO : O.moves = atTMoves a hS hH) :
    CH.AdTied (d.colRec a) (hermCols a hS hP hK S hI) (hermAtT a hS hH O) := by
  obtain ⟨disc, moves, xp⟩ := O
  obtain rfl : moves = atTMoves a hS hH := hO
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro u v c y hy
    have hy' := hy
    rw [show (hermAtT a hS hH ⟨disc, atTMoves a hS hH, xp⟩ u).pr 0 v c y = _ from
      hxPr_eq (atTTied a hH u) (fun i hi => levelAgreement a hS hH u i hi) 0 (Nat.zero_le _) v c y] at hy'
    exact adjacency_level_zero_up (hermCols a hS hP hK S hI) (atTMovesC a hS hH u) v c y
      (adjacency_level_zero_tied hS hP hK u v c _ (tam_so_up (Pr := d.Pr) d.W d.lev d.sp.cm d.hX d.hPr d.σ₀ u 0 (stepCrd a hS hH u 0 (Nat.zero_le _)) v c _ hy'))
  · intro u i h1 hm v c y hy
    have hy' := hy
    rw [show (hermAtT a hS hH ⟨disc, atTMoves a hS hH, xp⟩ u).pr i v c y = _ from
      hxPr_eq (atTTied a hH u) (fun i hi => levelAgreement a hS hH u i hi) i hm v c y] at hy'
    exact hxm_adI_up (hermCols a hS hP hK S hI) (atTMovesC a hS hH u) i h1 hm v c y
      (th_adI hS hP hK u i hm v c _ (tam_so_up (Pr := d.Pr) d.W d.lev d.sp.cm d.hX d.hPr d.σ₀ u i (stepCrd a hS hH u i hm) v c _ hy'))
  · intro u v c g hg
    exact adjacency_level_zero_down (hermCols a hS hP hK S hI) (atTMovesC a hS hH u) v c g
      (adjacency_level_zero_tied hS hP hK u v c _ (tam_so_dn (Pr := d.Pr) d.W d.lev d.sp.cm d.hX d.hPr u 0 v c g hg))
  · intro u i h1 hm v c g hg
    exact hxm_adI_dn (hermCols a hS hP hK S hI) (atTMovesC a hS hH u) i h1 hm v c g
      (th_adI hS hP hK u i hm v c _ (tam_so_dn (Pr := d.Pr) d.W d.lev d.sp.cm d.hX d.hPr u i v c g hg))
  · intro u v x c
    exact adjacency_level_zero_dilation (hermCols a hS hP hK S hI) (atTMovesC a hS hH u) v x c
      (adjacency_level_zero_tied hS hP hK u v c _ (tam_sameOff_dia (d.R.N 0) (d.Pr.vT u) d.Pr.vGs (d.repr u 0 c) v x (tieEV_over d.sp.cm d.hX d.hPr u v)))
  · intro u i h1 hm v x c
    exact hxm_adI_dil (hermCols a hS hP hK S hI) (atTMovesC a hS hH u) i h1 hm v x c
      (th_adI hS hP hK u i hm v c _ (tam_sameOff_dia (d.R.N i) (d.Pr.vT u) d.Pr.vGs (d.repr u i c) v x (tieEV_over d.sp.cm d.hX d.hPr u v)))

def atTOwedOf (disc : ∀ u, AtTDisc (d.colRec a) u)
    (xp : ∀ u, AtTXp (atTTied a hH u) (fun i hi => levelAgreement a hS hH u i hi)) : AtTOwed a hS hH :=
  ⟨disc, atTMoves a hS hH, xp⟩

end AdRec

end Formalism.L2.Col
