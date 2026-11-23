import Mathlib
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.IwasawaDecomposition
import CompanionTheory.AutomorphicTheory.BesselOrbitBounds.BesselMapUniqueness.BesselMapUniqGap
import CompanionTheory.HarishChandraModules.BesselParameterIntegrals.SmoothCyclicVectors.SmoothCyc
import CompanionTheory.HarishChandraModules.BesselParameterIntegrals.SmoothCyclicVectors.PhMeas
import CompanionTheory.HarishChandraModules.KFiniteAnalyticVectors.AdmissibleSmoothVectors.IwaCore
open CompanionTheory.Bmu
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.IwasawaDecomposition : IwaQ := by
  first | exact @GlobalTheory.CompanionTheory.BmuIwa.iwaQ | exact GlobalTheory.CompanionTheory.BmuIwa.iwaQ | (intros; apply GlobalTheory.CompanionTheory.BmuIwa.iwaQ <;> assumption)
