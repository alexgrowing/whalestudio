import Mathlib
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.GoodReductionCondition

noncomputable section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.RT GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Fc

namespace GlobalTheory.Fc.RL.PrimAt

variable {hL : GlobalTheory.Published.LocalLanglandsGL} {p : Prm hL}

theorem of_wit {K : Ctx} {q : WPt p.s K} {c : ℝ} {b : Bundle (q.w.D q.Z) q.O c} (w : BWit q b) : R1.P_hPA _ _ c b := by
  have h : (fun r : RPk b.R b.S => Formalism.IndefR.Links.PrimRows3 r.B.Q.Rl r.B.Q.F ∧ r.P.A3.fam3.TypesSep3) (rpkX w.y.y) :=
    ⟨w.y.intersectionNumber_baseChange.prim, w.y.intersectionNumber_baseChange.sep⟩
  rw [← w.y.eq] at h
  exact h

theorem row (p : Prm hL) (Q : V4.Slot) : R1.PeriodAdmissibilityAtBundlePoints Q (IsLinked p) := by
  refine RowE.row (R := R1.P_hPA) (RowE.of_all fun κ K β c b _ _ hl => ?_)
  obtain ⟨q, b', ⟨w⟩, he⟩ := hl
  have := congrArg (fun s : Σ (D : D7) (O : Obj D), Bundle D O c => R1.P_hPA s.1 s.2.1 c s.2.2) he
  exact cast this.symm (of_wit w)

theorem at_linked : ∀ (hL : GlobalTheory.Published.LocalLanglandsGL) (N : NExt hL) (S : SExt) (Γ : GeoP),
    RL.At (prmR N S Γ) R1.PeriodAdmissibilityAtBundlePoints :=
  fun _ N S Γ => At.of_row (row (prmR N S Γ) _)

end GlobalTheory.Fc.RL.PrimAt

end
