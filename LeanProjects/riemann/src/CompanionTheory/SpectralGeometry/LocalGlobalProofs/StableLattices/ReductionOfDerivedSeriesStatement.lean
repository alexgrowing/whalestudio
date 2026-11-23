import Mathlib
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.ReductionOfDerivedSeries
import CompanionTheory.AutomorphicTheory.BesselOrbitBounds.BesselMapUniqueness.BesselMapUniqGap
import CompanionTheory.HarishChandraModules.BesselParameterIntegrals.SmoothCyclicVectors.SmoothCyc
import CompanionTheory.HarishChandraModules.BesselParameterIntegrals.SmoothCyclicVectors.PhMeas
import CompanionTheory.HarishChandraModules.KFiniteAnalyticVectors.AdmissibleSmoothVectors.IwaCore
open CompanionTheory.Bmu
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.reduction_of_derived_series : DsLin → DsAd → DsDer → Reduce := by
  first | exact @GlobalTheory.CompanionTheory.BmuReduce.reduce | exact GlobalTheory.CompanionTheory.BmuReduce.reduce | (intros; apply GlobalTheory.CompanionTheory.BmuReduce.reduce <;> assumption)
