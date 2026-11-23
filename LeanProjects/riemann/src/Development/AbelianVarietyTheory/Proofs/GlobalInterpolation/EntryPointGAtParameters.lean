import Mathlib
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.GoodReductionCondition
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RowConditionsAtCompanionFromReadings

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.RT GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Fc

namespace GlobalTheory.Fc.RL

theorem rowE_dcPt_linked {hL : GlobalTheory.Published.LocalLanglandsGL} (p : Prm hL) (Q : V4.Slot) :
    RowE Q (IsLinked p) (fun _ => R1.P_hDcPtG) := by
  refine RowE.of_all fun κ K β c b _ _ hl => ?_
  obtain ⟨q, b', ⟨w⟩, he⟩ := hl
  have h1 := congrArg (fun s : Σ (D : D7) (O : Obj D), Bundle D O c => R1.P_hDcPtG s.1 s.2.1 c s.2.2) he
  refine cast h1.symm ?_
  show GlobalTheory.Cp.DcPtG _
  have hP : b'.P = R3.divisionPairOfAdelicFormsFaceColumnsData w.x := congrArg RPk.P w.y.eq
  rw [hP]
  exact (GlobalTheory.Mem.R3.rowConditions_at_companion_from_readings _ _ _ _ _ _ _ _ _ w.x).2.2.1

theorem at_hDcPtG : ∀ (hL : GlobalTheory.Published.LocalLanglandsGL) (N : NExt hL) (S : SExt) (Γ : GeoP),
    RL.At (prmR N S Γ) R1.DecompositionConditionAtBundlePoints := by
  intro hL N S Γ
  exact At.of_row (RowE.row (rowE_dcPt_linked _ _))

end GlobalTheory.Fc.RL

end
