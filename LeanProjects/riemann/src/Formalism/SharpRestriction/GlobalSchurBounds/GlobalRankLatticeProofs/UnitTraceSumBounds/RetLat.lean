import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.UnitTraceSumBounds.SigmaStarUniq
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.AreaLat
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.TransInvLat
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.SigmaStarUniq
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.DiscrNe
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.SigmaStarEx

namespace Formalism.MainNotions.Ext

theorem areaLat_holds : AreaLat := area_lattice_formula

theorem transInvLat_holds : TransInvLat := translation_invariant_lattice

theorem sigmaStarUniq_holds : SigmaStarUniq := sigma_star_unique

theorem discrNe_holds : DiscrNe := discrNe'

theorem sigmaStarEx_holds : SigmaStarEx := sigma_star_exists

end Formalism.MainNotions.Ext
