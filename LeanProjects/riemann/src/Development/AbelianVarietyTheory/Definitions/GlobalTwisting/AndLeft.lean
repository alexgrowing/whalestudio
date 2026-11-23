import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.TiedColumnData
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.LowerTieTwAt
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.ValidForConstructedPointClassesEventuallyWorking

noncomputable section

namespace GlobalTheory.Fc.Cv

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl NumberField

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {B : Base} {f : Fr B.toPre} {T : TwDat B}

structure ColView (w : ColW B f T) (Z : w.Lt) (tw : TwForms (w.D Z)) (nch : NChoice (w.D Z)) : Prop where
  jets : ColIn.JetsIn w.I
  rowInt : GlobalTheory.PerQ.RowInt w.I w.l Z
  tw_eq : tw = w.tw Z
  tup : ∃ tp : TupTied (w.D Z) (TC.cf w.I w.l Z) nch, tp.xi = w.I.xi

def HasCols : V4.Slot := positionOf fun _ _ _ _ w Z c => ColView w Z c.O.tw c.O.nch

def OverCols (Q : V4.Slot) : Prop := ∀ K X f T c, Q K X f T c → HasCols K X f T c

theorem OverCols.and_left {Q R : V4.Slot} (h : OverCols Q) : OverCols fun K X f T c => Q K X f T c ∧ R K X f T c :=
  fun K X f T c t => h K X f T c t.1

example : OverCols HasCols := fun _ _ _ _ _ t => t

end GlobalTheory.Fc.Cv

end
