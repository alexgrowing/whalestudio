import Formalism.LocalToGlobal.Columns.TiedLv
import Formalism.LocalToGlobal.Columns.TiedFv
import Formalism.LocalToGlobal.Columns.TiedValAll
import Formalism.LocalToGlobal.Columns.TiedUpDnRec
import Formalism.LocalToGlobal.Columns.TiedGlExt
import Formalism.LocalToGlobal.Columns.TiedGlChi
import Formalism.LocalToGlobal.Columns.TiedGlSplit
import Formalism.LocalToGlobal.Columns.TiedXpX
import Formalism.LocalToGlobal.Columns.TiedXpB
import Formalism.LocalToGlobal.Columns.TiedPtSurj
import Formalism.LocalToGlobal.Columns.TiedTilC
import Formalism.LocalToGlobal.Columns.TiedPerDat
import Formalism.LocalToGlobal.Columns.LevPackFrLat
import Formalism.LocalToGlobal.Columns.CharactersLevelZeroAgree
import Formalism.LocalToGlobal.Columns.CoordLatticeSelfDualEqStd
import Formalism.LocalToGlobal.Columns.TiedHIw
import Formalism.LocalToGlobal.Columns.TiedHDisc
import Formalism.LocalToGlobal.Columns.TiedHFv
import Formalism.LocalToGlobal.Columns.TiedMvC
import Formalism.LocalToGlobal.Columns.HsExtUHLast
import Formalism.LocalToGlobal.Columns.TiedAll

open NumberField IsDedekindDomain Module Matrix
open scoped TensorProduct

noncomputable section

namespace Formalism.L2.Col.V1

open Formalism.BasicNotions Formalism.L2.Forms

attribute [local instance] Formalism.BasicNotions.Host.cmStar

structure ColHyp (d : ColDat) : Prop where
  sp : SpStd d.toColBase
  host : HostHyp d
  row : RowSame d
  ch : d.Ch.Ok

  lev : d.lev = colLevS d.Ch
  levP : d.levP = (rowTyG d.Ch (rPsharp d.Ch)).inv

variable {d : ColDat} (a : ColArgs d) (h : ColHyp d)

abbrev spl (d : ColDat) : GSplit (X := d.X) (Pr := d.Pr) d.sp.cm := gSplit (X := d.X) (Pr := d.Pr) d.sp.cm d.hPr

abbrev tCls (u : d.what₂.Word) (i : ℕ) (hi : i ≤ d.R.m) : CF.ClsTied (D := d.colRec a) u i hi :=
  classAgreement a h.sp h.host (ptSurj_holds d) u i hi

abbrev tLv (u : d.what₂.Word) (i : ℕ) (hi : i ≤ d.R.m) : CF.LvTied (D := d.colRec a) u (atTTied a h.host u) i hi :=
  levelAgreement a h.sp h.host u i hi

abbrev tTil (u : d.what₂.Word) := tildeLatticeAgreement a h.sp h.host (points_surjective d) u

set_option maxHeartbeats 2000000 in

def formsTied (u : d.what₂.Word) : CF.FormsTied (d.colRec a) u where
  atT := atTTied a h.host u
  cls := fun i hi => tCls a h u i hi
  val := fun i hi => valuationAgreementConcrete a h.sp h.host (ptSurj_holds d) u i hi
  gl := recGLoc a (spl d) h.ch
  gl_K := recGLoc_K a (spl d) h.ch h.host
  glev := fun i hi => recGLev a (spl d) h.ch h.lev h.sp h.host (ptSurj_holds d) u i hi
  lv := fun i hi => tLv a h u i hi
  fMe := fun i hi => formModuleEquivAtPlace a h.sp h.host (ptSurj_holds d) u i hi
  fv := fun i hi => fvTied a h.sp h.host (ptSurj_holds d) u i hi
  upN := fun i hi => stepUpNatTied a h.sp h.host (ptSurj_holds d) u i hi
  dnN := fun i hi => stepDnNatTied a h.sp h.host (ptSurj_holds d) u i hi
  norm := fun i hi => stepNormTie a h.sp h.host (ptSurj_holds d) u i hi
  bw := fun i hi => stepBwTie a h.sp h.host (ptSurj_holds d) u i hi
  clsP := parabolicClassAgreement a h.sp h.host (points_surjective d) u
  valP := parabolicValuationAgreement a h.sp h.host (points_surjective d) u h.row
  normP := normPTied a h.sp h.host (points_surjective d) u h.row
  glevP := recGLevP a (spl d) h.ch h.levP h.sp h.host (points_surjective d) u
  til := tTil a h u
  tilLat := tilBaseLat a h.sp h.host (points_surjective d) (ptSurj_holds d) u
  tilFv := tilBaseFv a h.sp h.host (points_surjective d) (ptSurj_holds d) u
  tilAd := tilAd a h.sp h.host (points_surjective d) (ptSurj_holds d) u
    (tilMove a h.sp (points_surjective d) (ptSurj_holds d) u)
  frExt := recFrExt a (spl d) h.ch h.lev h.levP h.sp h.host (ptSurj_holds d) (points_surjective d) u
    (fun y x => by rw [iXc_eq a h.sp]; rfl)
  eWz := tieEWz a u
  evz := evzTied a h.sp h.host (points_surjective d) (ptSurj_holds d) u
    (tilMove a h.sp (points_surjective d) (ptSurj_holds d) u) _
    (fun s => by rw [stepValTied_eY]; rfl)
  jM := tieJM a u
  per := perTied a u (per_onto_dat d a)
  DGam := rfl

abbrev tAtO : AtTOwed a h.sp h.host :=
  ⟨attDisc a h.sp, atTMoves a h.sp h.host, levelExponentAtT a h.sp h.host (points_surjective d)⟩

abbrev tHermCols : CH.HermCols (d.colRec a) := hermCols a h.sp (ptSurj_holds d) (localLevelIsKOne_everywhere d) (spl d) (iwAll d (spl d))

abbrev tLev0 : LevelZeroConditions a h.sp h.host (ptSurj_holds d) (localLevelIsKOne_everywhere d) (spl d) (iwAll d (spl d)) (tAtO a h) :=
  baseLevelConditions a h.sp h.host (ptSurj_holds d) (localLevelIsKOne_everywhere d) (spl d) (iwAll d (spl d)) (tAtO a h)

def tHerm : CH.ColsHerm (d.colRec a) :=
  colsHerm a h.sp h.host (ptSurj_holds d) (localLevelIsKOne_everywhere d) (spl d) (iwAll d (spl d)) (tAtO a h)
    { levelZeroCompatibility := levelZeroCompatibility a h.sp h.host (ptSurj_holds d) (localLevelIsKOne_everywhere d) (spl d) (iwAll d (spl d)) (tAtO a h) (tLev0 a h)
      ad := adTied a h.sp h.host (ptSurj_holds d) (localLevelIsKOne_everywhere d) (spl d) (iwAll d (spl d)) (tAtO a h) rfl
      piG := piGConst a h.sp h.host (ptSurj_holds d) (localLevelIsKOne_everywhere d) (spl d) (iwAll d (spl d)) (tAtO a h) (tLev0 a h)
      stabMap := stabMapTied a h.sp h.host (points_surjective d) (ptSurj_holds d) (localLevelIsKOne_everywhere d) (spl d) (iwAll d (spl d)) _ _
      fvI := formValueAgreement a h.sp h.host (ptSurj_holds d) (localLevelIsKOne_everywhere d) (spl d) (iwAll d (spl d)) (tAtO a h) }

set_option maxHeartbeats 4000000 in

theorem tJoint (u : d.what₂.Word) : CF.Joint (tHerm a h) u (formsTied a h u) where
  eV := rfl
  piU := rfl
  res := rfl
  car0 := characters_level_zero_agree a h.sp h.host (ptSurj_holds d) (localLevelIsKOne_everywhere d) (spl d) (iwAll d (spl d)) u
  carI := fun i h1 hm => th_carI a h.sp h.host (ptSurj_holds d) (localLevelIsKOne_everywhere d) (spl d) (iwAll d (spl d)) u i h1 hm
  carP := th_carP a h.sp h.host (points_surjective d) u
  lattice₂ := th_latP a h.sp h.host (points_surjective d) u
  pr := fun i hi v c z z' hz => th_pr (atTTied a h.host u) (fun i hi => levelAgreement a h.sp h.host u i hi) i hi v c z z' hz
  prk := fun i hi v c z z' hz => th_prk (atTTied a h.host u) (fun i hi => levelAgreement a h.sp h.host u i hi) i hi v c z z' hz
  z0 := joint_lastVector a h.sp h.host (points_surjective d) u
  ga := th_ga a h.sp h.host (points_surjective d) u
  sp := th_joint_sp a h.sp (ptSurj_holds d) (localLevelIsKOne_everywhere d) (spl d) (iwAll d (spl d)) h.ch u
  piG := th_joint_piG a h.sp h.host (ptSurj_holds d) (localLevelIsKOne_everywhere d) (spl d) (iwAll d (spl d)) (tAtO a h) h.ch (tLev0 a h) u
  fr0 := jointLevel_frame_zero a h.sp h.host (ptSurj_holds d) (localLevelIsKOne_everywhere d) (spl d) (iwAll d (spl d)) h.ch h.lev u

def colsTied : CF.ColsTied (d.colRec a) where
  herm := tHerm a h
  forms := fun u => formsTied a h u
  joint := fun u => tJoint a h u
  gl_const := fun _ _ => rfl
  chi := recGLoc_chi a (spl d) h.ch
  fr_const := fun u u' i hi him => recGLev_fr_const a (spl d) h.ch h.lev h.sp h.host (ptSurj_holds d) u u' i hi him
  frP_const := fun u u' => (recGLevP_fr a (spl d) h.ch h.levP h.sp h.host (points_surjective d) u).trans
    (recGLevP_fr a (spl d) h.ch h.levP h.sp h.host (points_surjective d) u').symm

def formsOwed (u : d.what₂.Word) : Formalism.L2.Col.FormsOwed a h.sp h.host (ptSurj_holds d) u where
  gl := (formsTied a h u).gl
  gl_K := (formsTied a h u).gl_K
  glev := (formsTied a h u).glev
  fMe := (formsTied a h u).fMe
  fv := (formsTied a h u).fv
  upN := (formsTied a h u).upN
  dnN := (formsTied a h u).dnN
  clsP := (formsTied a h u).clsP
  valP := (formsTied a h u).valP
  normP := (formsTied a h u).normP
  glevP := (formsTied a h u).glevP
  til := (formsTied a h u).til
  tilLat := (formsTied a h u).tilLat
  tilFv := (formsTied a h u).tilFv
  tilAd := (formsTied a h u).tilAd
  frExt := (formsTied a h u).frExt
  eWz := (formsTied a h u).eWz
  evz := (formsTied a h u).evz
  jM := (formsTied a h u).jM
  per := (formsTied a h u).per

set_option maxHeartbeats 4000000 in

def colsOwed : Formalism.L2.Col.ColsOwed a h.sp h.host (ptSurj_holds d) where
  forms := formsOwed a h
  herm := tHerm a h
  joint := tJoint a h
  gl_const := (colsTied a h).gl_const
  chi := (colsTied a h).chi
  fr_const := (colsTied a h).fr_const
  frP_const := (colsTied a h).frP_const

def colsTiedD {D : D7} (e : D.colRec = d.colRec a) : Formalism.L2.Forms.ColsTied D :=
  columnsAgreement_of_eq e (colsTied a h)

end Formalism.L2.Col.V1
