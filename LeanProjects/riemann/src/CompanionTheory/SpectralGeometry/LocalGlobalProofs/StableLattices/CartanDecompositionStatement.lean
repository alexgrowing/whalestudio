import Mathlib
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.CartanDecomposition
import CompanionTheory.AutomorphicTheory.BesselOrbitBounds.BesselMapUniqueness.BesselMapUniqGap
import CompanionTheory.HarishChandraModules.BesselParameterIntegrals.SmoothCyclicVectors.SmoothCyc
import CompanionTheory.HarishChandraModules.BesselParameterIntegrals.SmoothCyclicVectors.PhMeas
import CompanionTheory.HarishChandraModules.KFiniteAnalyticVectors.AdmissibleSmoothVectors.IwaCore
open CompanionTheory.Bmu
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.CartanDecomposition : CartanQ := by
  first | exact @GlobalTheory.CompanionTheory.BesselCartan.cartanQ | exact GlobalTheory.CompanionTheory.BesselCartan.cartanQ | (intros; apply GlobalTheory.CompanionTheory.BesselCartan.cartanQ <;> assumption)
