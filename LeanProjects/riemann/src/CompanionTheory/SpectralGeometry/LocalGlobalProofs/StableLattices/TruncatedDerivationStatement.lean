import Mathlib
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.TruncatedDerivation
import CompanionTheory.AutomorphicTheory.BesselOrbitBounds.BesselMapUniqueness.BesselMapUniqGap
import CompanionTheory.HarishChandraModules.BesselParameterIntegrals.SmoothCyclicVectors.SmoothCyc
import CompanionTheory.HarishChandraModules.BesselParameterIntegrals.SmoothCyclicVectors.PhMeas
import CompanionTheory.HarishChandraModules.KFiniteAnalyticVectors.AdmissibleSmoothVectors.IwaCore
open CompanionTheory.Bmu
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.TruncatedDerivation : CutDer := by
  first | exact @GlobalTheory.CompanionTheory.CutDeriv.cutDer | exact GlobalTheory.CompanionTheory.CutDeriv.cutDer | (intros; apply GlobalTheory.CompanionTheory.CutDeriv.cutDer <;> assumption)
