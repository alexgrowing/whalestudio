import Mathlib
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.SpanGenerators
import CompanionTheory.AutomorphicTheory.BesselOrbitBounds.BesselMapUniqueness.BesselMapUniqGap
import CompanionTheory.HarishChandraModules.BesselParameterIntegrals.SmoothCyclicVectors.SmoothCyc
import CompanionTheory.HarishChandraModules.BesselParameterIntegrals.SmoothCyclicVectors.PhMeas
import CompanionTheory.HarishChandraModules.KFiniteAnalyticVectors.AdmissibleSmoothVectors.IwaCore
open CompanionTheory.Bmu
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.SpanGenerators : SpanG := by
  first | exact @GlobalTheory.CompanionTheory.BmuSpan.spanG | exact GlobalTheory.CompanionTheory.BmuSpan.spanG | (intros; apply GlobalTheory.CompanionTheory.BmuSpan.spanG <;> assumption)
