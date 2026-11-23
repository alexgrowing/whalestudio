import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.HasPartAnd
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.JetSplitAmb
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.PeriodRelationsTrueColumnsAtTupleStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.KerTie
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.RowPinSetDivZ
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Ker Formalism.L2.Forms GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Fc GlobalTheory.Svd NumberField IsDedekindDomain

set_option maxHeartbeats 1000000 in

theorem GlobalTheory.Svd.tiesAt_of_rowPin : ∀ (K : Ctx) (β : BPt K), β.Is (positionOf (HasPartAnd fun _ _ _ _ w Z => ∀ a, GlobalTheory.AtG.RowPin w.I w.ok w.l Z a)) → ∀ μ, GlobalTheory.AtG.TiesAt β.D β.O.ex.errX β.O.X μ := by
  intro K β hβ μ
  have key := positionOf_ind (R := fun K X f T c => ∀ O : Obj X.toD7, ofObj O = c.O → ∀ N h μ,
      GlobalTheory.AtG.TiesAt (setDiv X.toD7 N h) (O.tr N h).ex.errX (O.tr N h).X μ) ?_ hβ
  · exact key (β.Y.obj β.p) ((show ofObj (β.Y.obj β.p) = layObj β.Y from rfl).trans β.hY) (nPrime β.p.L) β.p.ht μ
  · intro K B f T w Z c hc O hO N h μ
    obtain ⟨⟨P⟩, hrow⟩ := hc
    have hpart : Part w Z (ofObj O) := hO ▸ P
    obtain ⟨_, hpiG, hpiT, hqp, _⟩ := Part.kerTie B f T w Z O hpart
    exact GlobalTheory.T.periodRelations_trueColumns_at_tuple w.I w.ok w.l (GlobalTheory.Mem.Db.setDivZ Z N h) w.l0 P.pin.jets _ _ μ hpiG hpiT hqp
      (GlobalTheory.AtG.rowPin_setDivZ w.I w.ok w.l Z N h μ (hrow μ))
