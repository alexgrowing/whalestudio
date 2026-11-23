import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.TermsFiniteAtPoint.TermsAtFiniteOfFrameOpShortFin
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.TermsFiniteAtPoint.FrameTop
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.TermsFiniteAtPoint.DShort

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem terms_at_point_finite (D : Formalism.BasicNotions.D7) (u u' : D.what₂.Word) : Formalism.L2.SG.TermDef.TermsAtFinite D u u' :=
  PI.TermsAtPtFiniteW.termsAtFinite_of_frameOp_shortFin PI.TermsAtPtFiniteW.frameOp_holds PI.TermsAtPtFiniteW.shortFin_holds D u u'
