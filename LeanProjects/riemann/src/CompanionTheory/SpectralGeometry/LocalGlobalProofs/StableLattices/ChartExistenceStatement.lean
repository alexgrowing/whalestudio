import Mathlib
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.ChartExistence
import CompanionTheory.AutomorphicTheory.BesselOrbitBounds.BesselMapUniqueness.BesselMapUniqGap
import CompanionTheory.HarishChandraModules.BesselParameterIntegrals.SmoothCyclicVectors.SmoothCyc
import CompanionTheory.HarishChandraModules.BesselParameterIntegrals.SmoothCyclicVectors.PhMeas
import CompanionTheory.HarishChandraModules.KFiniteAnalyticVectors.AdmissibleSmoothVectors.IwaCore
open CompanionTheory.Bmu
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ChartExistence : ChartExists := by
  first | exact @GlobalTheory.CompanionTheory.ProdExChart.chartExists | exact GlobalTheory.CompanionTheory.ProdExChart.chartExists | (intros; apply GlobalTheory.CompanionTheory.ProdExChart.chartExists <;> assumption)
