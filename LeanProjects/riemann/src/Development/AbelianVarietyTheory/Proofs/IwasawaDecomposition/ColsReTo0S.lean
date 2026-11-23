import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsIsBIffCoreB
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ColsReLev0
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Formalism.LocalRingCardinality.SpanPowerMembership.TwCore
import Formalism.SharpRestriction.GlobalSchurBounds.ThickPlacesCorollaryOfAnyTranslate
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.Df GlobalTheory.Mem.Db NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.Db.DivTr

open Formalism.L2.Forms GlobalTheory.Mem.Top.ColOwe

section Gen

variable {D : D7} (N : ∀ u, Submodule (𝓞 D.what₂.LL) (D.div.Nu u).V) (h : D.what₂.Word → ℝ)

set_option maxHeartbeats 4000000 in

def atTTS {u : D.what₂.Word} (A : AtTTied (D := D) u) : AtTTied (D := setDiv D N h) u := { A with }

set_option maxHeartbeats 4000000 in

def forms0S {u : D.what₂.Word} (F : Forms0 D u) : Forms0 (setDiv D N h) u :=
  { F with
    atT := atTTS N h F.atT
    cls0 := { F.cls0 with }
    val0 := { F.val0 with }
    lv0 := { F.lv0 with } }

set_option maxHeartbeats 4000000 in

def herm0S (H : Formalism.L2.Herm.Herm0 D) : Formalism.L2.Herm.Herm0 (setDiv D N h) := { H with }

set_option maxHeartbeats 4000000 in

def fullS (X : Formalism.L2.Herm.FullTiedS D) : Formalism.L2.Herm.FullTiedS (setDiv D N h) :=
  { X with
    base := { X.base with }
    atT := fun u => { X.atT u with }
    ad := { X.ad with } }

set_option maxHeartbeats 4000000 in
theorem fullS_to0 (X : Formalism.L2.Herm.FullTiedS D) : (fullS N h X).to0 = herm0S N h X.to0 := rfl

set_option maxHeartbeats 4000000 in

def gS {Gt : GatTies D} {c : LatCmp D} (g : Formalism.L2.G.GroupCompatibilityAll D Gt c) :
    Formalism.L2.G.GroupCompatibilityAll (setDiv D N h) (gatTr N h Gt) (cmpTr N h c) where
  herm := herm0S N h g.herm
  forms := fun u => forms0S N h (g.forms u)
  cmp := { g.cmp with }
  ring := g.ring
  gat := g.gat

end Gen

variable {B : Base} {f : Fr B.toPre} {T : TwDat B}
variable (w : ColW B f T) (Z : w.Lt) (N : ∀ u, Submodule (𝓞 B.LL) (Z.V.div.Nu u).V) (h : B.Word → ℝ)

set_option maxHeartbeats 4000000 in
theorem fullS_cols (X : Formalism.L2.Herm.FullTiedS (w.D Z)) :
    (fullS (D := w.D Z) N h X).cols = hermRe (setDivZ Z N h) X.cols := rfl

set_option maxHeartbeats 4000000 in
theorem colsRe_to0S (C : ColsTiedSym (w.D Z)) (u : B.Word) :
    ((colsRe (setDivZ Z N h) C).forms u).to0 = forms0S (D := w.D Z) N h (C.forms u).to0 := rfl

set_option maxHeartbeats 8000000 in

theorem stdC_tr (C : ColsTiedSym (w.D Z)) (hC : TC.StdC w.I w.l Z C) :
    TC.StdC w.I w.l (setDivZ Z N h) (colsRe (setDivZ Z N h) C) := fun u =>
  { hC u with gl := { (hC u).gl with } }

set_option maxHeartbeats 8000000 in

def colTTr (t : ColT w Z) : ColT w (setDivZ Z N h) where
  C := colsRe (setDivZ Z N h) t.C
  std := stdC_tr w Z N h t.C t.std
  stdLv := fun u => t.stdLv u
  full := ⟨fullS (D := w.D Z) N h t.full.1, (fullS_cols w Z N h t.full.1).trans (congrArg (hermRe (setDivZ Z N h)) t.full.2)⟩
  stdDt := t.stdDt
  Gt := gatTr (D := w.D Z) N h t.Gt
  cmp := cmpTr (D := w.D Z) N h t.cmp
  g := gS (D := w.D Z) N h t.g
  herm_eq := (congrArg (herm0S (D := w.D Z) N h) t.herm_eq).trans (fullS_to0 (D := w.D Z) N h t.full.1).symm
  forms_eq := (congrArg (fun F u => forms0S (D := w.D Z) N h (F u)) t.forms_eq).trans
    (funext fun u => (colsRe_to0S w Z N h t.C u).symm)
  gpl := t.gpl

end GlobalTheory.Mem.Db.DivTr

end
