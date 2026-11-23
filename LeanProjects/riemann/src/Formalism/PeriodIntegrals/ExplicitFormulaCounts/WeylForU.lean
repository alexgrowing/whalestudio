import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.WeylForU
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.ModelIso
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.PolyCoef
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.UnitaryDense
import Formalism.PeriodIntegrals.AdmissibleModel.WeylDim

theorem nablaDim_closed : PI.NablaDim := fun n nu h => Formalism.L2.G.Model.weyl_dualWeyl ℂ n nu h

theorem modelIso_closed : PI.ModelIso := modelIso_of polynomial_coefficients unitaryGroupDense_holds highest_weight_irreducible

theorem weylForU_closed : PI.WeylForU := weylForU_of modelIso_closed nablaDim_closed
