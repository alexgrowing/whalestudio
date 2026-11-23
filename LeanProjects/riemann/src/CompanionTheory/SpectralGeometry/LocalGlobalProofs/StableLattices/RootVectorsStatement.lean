import Mathlib
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.RootVectors
import CompanionTheory.AutomorphicTheory.BesselOrbitBounds.BesselMapUniqueness.BesselMapUniqGap
import CompanionTheory.HarishChandraModules.BesselParameterIntegrals.SmoothCyclicVectors.SmoothCyc
import CompanionTheory.HarishChandraModules.BesselParameterIntegrals.SmoothCyclicVectors.PhMeas
import CompanionTheory.HarishChandraModules.KFiniteAnalyticVectors.AdmissibleSmoothVectors.IwaCore
open CompanionTheory.Bmu
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.RootVectors : RootVec := by
  first | exact @GlobalTheory.CompanionTheory.BmuRootVec.rootVec | exact GlobalTheory.CompanionTheory.BmuRootVec.rootVec | (intros; apply GlobalTheory.CompanionTheory.BmuRootVec.rootVec <;> assumption)
