import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.UnitTraceSumBounds.OkpInertOf
import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.UnitTraceSumBounds.StmtEndIntWOfOkp
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.OkpInert
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.InertPrime

namespace Formalism.MainNotions.Ext

theorem okpInertG_holds : OkpInertG := integers_inert_prime

theorem inertPrime_holds : InertPrime := isPrime_span_of_jacobi_neg_one

theorem okpInert_holds (D : Formalism.BasicNotions.D7) : Formalism.MainNotions.GL3Theta.okpInert D := okpInert_of okpInertG_holds inertPrime_holds D

theorem stmt_endIntW_holds (D : Formalism.BasicNotions.D7) : Formalism.MainNotions.GL3Theta.StatementEndomorphismIntegralWitt D := stmt_endIntW_of_okp D (okpInert_holds D)

end Formalism.MainNotions.Ext
