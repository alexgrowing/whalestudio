import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemRangeOfPowG
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ColsReLev0
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsStandardColumnComparisonsTrueColumnsStatement
import Formalism.LocalToGlobal.GroupLattices.TiedFamilies.TieTrF
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HermEqExtraTied
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.TiedColumnData
import Formalism.SharpRestriction.GlobalSchurBounds.ThickPlacesCorollaryOfAnyTranslate

noncomputable section

namespace GlobalTheory.Mem.Top.ColOwe

open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Forms GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC NumberField IsDedekindDomain

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Re

variable {B : Base} {C : Cols B} {Z : Later B C} (Z' : Later B C)

set_option maxHeartbeats 4000000 in

def forms0Re {u : B.Word} (T : Forms0 (recOf Z) u) : Forms0 (recOf Z') u :=
  { T with
    atT := atTTRe Z' T.atT
    cls0 := clsRe Z' T.cls0
    val0 := valRe Z' T.val0
    lv0 := lvRe Z' T.lv0 }

set_option maxHeartbeats 4000000 in
theorem columnFormsAlongLaterStages_stageZero_eq (T : ColsTiedSym (recOf Z)) (u : B.Word) :
    ((colsRe Z' T).forms u).to0 = forms0Re Z' (T.forms u).to0 := rfl

open Formalism.MainNotions.G in
set_option maxHeartbeats 4000000 in

theorem forms0Re_setGat (g : ∀ u (w : (recOf Z).what₂.places.Pl),
      GIdx (recOf Z).host ((recOf Z).mem u).A.T ((recOf Z).what₂.places.resChar w) → GAtP ((recOf Z).what₂.places.resChar w))
    (hd : ∀ u w h, (g u w h).d = Module.finrank ℂ ((recOf Z).mem u).A.Mu0) {u : B.Word} (T : Forms0 (recOf Z) u) :
    forms0Re { Z with G := { Z.G with gat := g, gat_d := hd } } T = Formalism.L2.G.forms0Set (recOf Z) g hd T := rfl

end Re

variable {B : Base} {X : PreX B.toPre} (I : TC B X)

section Std

variable (l : I.Laws) {Z : Later B (I.cols l)} (Z' : Later B (I.cols l))

set_option maxHeartbeats 8000000 in

theorem stdC_colsRe (T : ColsTiedSym (I.rec7 l Z)) (h : I.StdC l Z T) : I.StdC l Z' (colsRe Z' T) := fun u =>
  { h u with gl := { (h u).gl with } }

set_option maxHeartbeats 8000000 in

theorem stdLvC_colsRe (T : ColsTiedSym (I.rec7 l Z)) (u : B.Word) (h : I.StdLvC l Z u (T.forms u)) :
    I.StdLvC l Z' u ((colsRe Z' T).forms u) := h

end Std

variable (h : I.Ok) (p : TC.Pins B X) (l : I.Laws)

def tieBase (hZ : Nonempty (Later B (I.cols l))) : ColsTiedSym (I.rec7 l hZ.some) := (GlobalTheory.T.exists_standardColumnComparisons_trueColumns I h p l hZ.some).choose

variable (Z : Later B (I.cols l))

def tieT : ColsTiedSym (I.rec7 l Z) := colsRe Z (tieBase I h p l ⟨Z⟩)

def levT : LevelData (I.rec7 l Z) := (tieT I h p l Z).herm.base.lev0

def formsT (u : B.Word) : Forms0 (I.rec7 l Z) u := ((tieT I h p l Z).forms u).to0

def errT : ErrX (I.rec7 l Z) := errOf (tieT I h p l Z).herm

theorem dGam_cols (u : B.Word) (a : I.ι) : ((I.cols l).chTw u a).DGam = DGam B.fields.E B.R := rfl

theorem colLay_of_tie (T : ColsTiedSym (I.rec7 l Z)) : ColLay (I.rec7 l Z) T.herm.base.lev0 (errOf T.herm) :=
  colLay_of_tied ⟨B, I.cols l, Z.W, Z.V, Z.S, Z.N, Z.G⟩ ⟨X⟩ (dGam_cols I l) T

open Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl in

theorem colLay_colT : ∀ (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T) (Z : w.Lt) (t : ColT w Z),
    ColLay (w.D Z) t.full.1.base.lev0 (Formalism.L2.Herm.toErrXS t.full.1) := by
  intro B f T w Z t
  have e : errOf t.C.herm = Formalism.L2.Herm.toErrXS t.full.1 :=
    GlobalTheory.Mem.Col2.TC.ExtraTie.errX_eq t.full.1 t.C.herm t.full.2 (errOf t.C.herm) (errOf_piG _) (errOf_piT _) (errOf_vPl _)
  have hl : t.full.1.base.lev0 = t.C.herm.base.lev0 :=
    congrArg (fun H : Formalism.L2.Herm.ColsHermS (w.D Z) => H.base.lev0) t.full.2
  rw [hl, ← e]
  exact colLay_of_tie w.I w.l Z t.C

end GlobalTheory.Mem.Top.ColOwe

end
