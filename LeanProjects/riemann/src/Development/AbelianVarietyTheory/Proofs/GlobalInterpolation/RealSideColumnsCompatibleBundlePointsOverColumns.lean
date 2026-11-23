import Mathlib
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.AndLeft
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.ReferenceChainEvaluationAtBundlePoints
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsSymmetricColumnFormsStepZeroFiniteCharacteStatement
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.PropertyAtConstructedPointsOfTrueColumnsViewStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Fc GlobalTheory.Fc.Cv NumberField
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Fc.PeriodEntriesOverColumns

def TiePt (D : D7) (_ : Obj D) : Prop :=
  Formalism.L2.Theta.RealTied D ∧ ∃ C : Formalism.L2.Forms.ColsTiedSym D, ∀ u, Formalism.MainNotions.RT.ChiFin0 (C.forms u)

theorem row_tie_of_overCols : ∀ (Q : V4.Slot), OverCols Q → ∀ (Bd : BdT) (Lk : LkT Bd), PeriodEntriesOverColumns.Row_tie Q Lk := by
  intro Q hQ Bd Lk
  have hpt : ∀ (K : Ctx) (β : BPt K), β.Is HasCols → TiePt β.D β.O :=
    GlobalTheory.T.property_at_constructedPoints_of_trueColumnsView TiePt fun B f T w Z O nch _ _ hR =>
      ⟨hR, GlobalTheory.T.exists_symmetricColumnForms_stepZeroFiniteCharacter w.I w.ok w.pins w.l Z⟩
  have h0 : Row0 Q (EvC TiePt) :=
    validForConstructedPointClasses_eventuallyWorkingClass (Q := Q) (EvP.of_all fun _ K _ β hq => hpt K β (hQ K β.X β.f β.T β.c hq))
  refine Row0.row (Row.imp h0 fun 𝒜 _ _ h => ?_) Lk
  refine Closed.imp h fun Fm _ _ H => ?_
  obtain ⟨x0, hx0⟩ := H
  refine ⟨max x0 (Fm.x1 + 1), fun x hx i => ?_⟩
  have e0 : x0 ≤ x := le_trans (le_max_left _ _) hx
  have e1 : Fm.x1 < x := by have := le_trans (le_max_right x0 (Fm.x1 + 1)) hx; linarith
  exact hx0 x e0 e1 i

end GlobalTheory.Fc.PeriodEntriesOverColumns
