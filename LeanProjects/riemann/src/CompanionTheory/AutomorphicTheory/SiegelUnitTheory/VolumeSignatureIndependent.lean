import Mathlib
import CompanionTheory.AutomorphicTheory.SiegelUnitTheory.UnitsAinf
import CompanionTheory.AutomorphicTheory.SiegelUnitTheory.ClassNumberMass

namespace CompanionTheory.HU

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.StandardLattice Formalism.L2.GlobalTheoryTheory.GenusMassVolumes

theorem siegel_mass_rank_one : SiegelOneAll := fun F E _ _ _ _ _ σ h M J hJ => sw1b2 F E σ h M J hJ

theorem mass_ratio_under_volume : ∀ D : D7, RT.MassRatioUnderVolume D := hU_of siegel_mass_rank_one

theorem volume_signature_independent : ∀ D : D7, VolSigIndep D := volSigIndep_of siegel_mass_rank_one

end CompanionTheory.HU
