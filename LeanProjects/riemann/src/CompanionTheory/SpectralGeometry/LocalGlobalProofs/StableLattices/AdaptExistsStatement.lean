import Mathlib
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.AdaptExists
import CompanionTheory.AutomorphicTheory.BesselOrbitBounds.BesselMapUniqueness.BesselMapUniqGap
import CompanionTheory.HarishChandraModules.BesselParameterIntegrals.SmoothCyclicVectors.SmoothCyc
import CompanionTheory.HarishChandraModules.BesselParameterIntegrals.SmoothCyclicVectors.PhMeas
import CompanionTheory.HarishChandraModules.KFiniteAnalyticVectors.AdmissibleSmoothVectors.IwaCore
open CompanionTheory.Bmu
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.AdaptedBasisExistsAlt : AdaptExists := by
  first | exact @GlobalTheory.CompanionTheory.BmuAdapt.adaptExists | exact GlobalTheory.CompanionTheory.BmuAdapt.adaptExists | (intros; apply GlobalTheory.CompanionTheory.BmuAdapt.adaptExists <;> assumption)
