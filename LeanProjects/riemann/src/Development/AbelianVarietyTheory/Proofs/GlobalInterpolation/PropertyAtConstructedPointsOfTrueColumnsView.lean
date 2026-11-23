import Mathlib
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.AndLeft
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.EFirstGeOfULastNonpos
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.BaseSignsOfVal

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Fc GlobalTheory.Fc.Cv NumberField
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Fc.Cv

theorem view_at_built : ∀ (R : ∀ D : D7, Obj D → Prop), (∀ (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T) (Z : w.Lt) (O : Obj (w.D Z)) (nch : NChoice (w.D Z)), ColView w Z O.ex.tw nch → GlobalTheory.LvT.WtSign.BaseSigns B → Formalism.L2.Theta.RealTied (w.D Z) → R (w.D Z) O) → ∀ (K : Ctx) (β : BPt K), β.Is HasCols → R β.D β.O := by
  intro R H K β hβ
  have hS := GlobalTheory.Fc.Sg.baseSigns_of_bPt K β
  refine positionOf_ind (P := fun _ _ _ _ w Z c => ColView w Z c.O.tw c.O.nch)
    (R := fun K X f T c => ∀ (Y : Lay X.toD7), layObj Y = c.O → ∀ p : LedPart K.C Y,
      GlobalTheory.LvT.WtSign.BaseSigns X.B → Formalism.L2.Theta.RealTied X.toD7 → R p.pt.D (Obj.ofPt p.pt)) ?_ hβ β.Y β.hY β.p hS β.c.real
  intro K B f T w Z c hv Y hY p hS hreal
  let Z' : w.Lt := { Z with V := { Z.V with div := (setDiv (w.D Z) (nPrime p.L) p.ht).div } }
  have etw : Y.tw = w.tw Z := (congrArg Obj2.tw hY).trans hv.tw_eq
  obtain ⟨tp, htp⟩ := hv.tup
  refine H B f T w Z' (Obj.ofPt p.pt) (nchTr (nPrime p.L) p.ht c.O.nch) ⟨hv.jets, ⟨hv.rowInt.ref, hv.rowInt.tw⟩, ?_, ⟨{ tp with }, htp⟩⟩ hS
    ⟨hreal.cdScale, hreal.dsig, hreal.dsig_all, hreal.vol⟩
  show twTr (nPrime p.L) p.ht Y.tw = w.tw Z'
  rw [etw]
  rfl

end GlobalTheory.Fc.Cv
