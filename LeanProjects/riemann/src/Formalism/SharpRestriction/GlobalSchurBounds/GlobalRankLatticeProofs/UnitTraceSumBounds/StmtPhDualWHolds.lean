import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.UnitTraceSumBounds.CoefWfZero
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.FglPtW

namespace Formalism.MainNotions.Ext

theorem addPtW_holds : AddPtW :=
  fun p _ g hOk hF σ a b ha hb =>
    formal_group_add_generation ℂ_[p] (Formalism.MainNotions.GL3Theta.Wp p) g.l g.ex hOk.2.2.1 hOk.2.2.2 hF σ a b ha hb

theorem mulPtW_holds : MulPtW :=
  fun p _ g hOk c hc σ a ha =>
    formal_group_mul_generation ℂ_[p] (Formalism.MainNotions.GL3Theta.Wp p) g.l g.ex hOk.2.2.1 hOk.2.2.2 c hc σ a ha

theorem linPtW_holds : LinPtW :=
  fun p _ g hOk hF ι _ c hc σ a ha =>
    formal_group_lin_generation ℂ_[p] (Formalism.MainNotions.GL3Theta.Wp p) g.l g.ex hOk.2.2.1 hOk.2.2.2 hF ι c hc σ a ha

theorem stmt_beW_holds (D : Formalism.BasicNotions.D7) : Formalism.MainNotions.GL3Theta.StatementBilinearWitt D :=
  beW_of addPtW_holds mulPtW_holds D fun _ _ _ _ hα => by apply okp_swap; exact hα

theorem stmt_PhDualW_holds (D : Formalism.BasicNotions.D7) : Formalism.MainNotions.GL3Theta.StatementPhaseDualWitt D := phDualW_of addPtW_holds linPtW_holds D

theorem stmt_SDiffW_holds (D : Formalism.BasicNotions.D7) : Formalism.MainNotions.GL3r7.StatementSymmetricDifferenceWitt D := sDiffW_of addPtW_holds mulPtW_holds linPtW_holds D

end Formalism.MainNotions.Ext
