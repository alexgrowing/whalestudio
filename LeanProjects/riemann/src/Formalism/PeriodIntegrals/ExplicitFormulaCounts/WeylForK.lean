import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.WeylForK
import Formalism.PeriodIntegrals.ExplicitFormulaCounts.WeylForU

theorem weylForK_closed : PI.WeylForK := weylForK_of weylForU_closed
