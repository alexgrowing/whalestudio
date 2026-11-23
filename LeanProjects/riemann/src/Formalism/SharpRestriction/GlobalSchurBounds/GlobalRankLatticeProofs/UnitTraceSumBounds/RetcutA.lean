import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.UnitTraceSumBounds.SimeqLimit
import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.UnitTraceSumBounds.PhNormOfUnits
import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.UnitTraceSumBounds.CubeOfTwoIdentities
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.SimeqPdInt
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.BiaddZpLin
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.PhNormUnits
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.PhNormLimit
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.BeDiagZp

namespace Formalism.MainNotions.Ext.CutA

theorem simeqPd_holds : SimeqPd := simeq_pd_integral

theorem biaddZp_holds : BiaddZp :=
  fun p _ g hOk hi hb n => biadditive_zp_linear p g.l g.ex g.ph hOk.2.2.1 hOk.2.2.2 hi hb n

theorem phNormOfUnits_holds : PhNormOfUnits := by
  intro p _ g S hok
  exact phase_norm_units p g.l g.ex g.ph S hok.2.2.1 hok.2.2.2

theorem phNormClosed_holds : PhNormClosed := by
  intro p _ g S hok
  exact phase_norm_limit_target p g.l g.ex g.ph S hok.2.2.1 hok.2.2.2

theorem beDiagG_holds : BeDiagG :=
  fun p _ g S hOk => diagonal_zp_identity p g.l g.ex g.ph S hOk.2.2.1 hOk.2.2.2

end Formalism.MainNotions.Ext.CutA
