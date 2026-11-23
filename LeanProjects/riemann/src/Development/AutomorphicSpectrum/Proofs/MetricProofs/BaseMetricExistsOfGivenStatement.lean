import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.BaseMetricExistsOfGiven
import Mathlib
import Development.AutomorphicSpectrum.Statements.TowerExistence.GoodTowerExistsX
import Development.AutomorphicSpectrum.Statements.MetricStatements.ExistsFlagModelBaseMetric
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.RootOnFund
open AlgebraicGeometry CategoryTheory NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.base_metric_exists_of_given : Given → PB.BaseMetricExists := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.BMx.baseMetricExists_of_given | exact GlobalTheory.CompanionTheory.Ar.PB.BMx.baseMetricExists_of_given | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.BMx.baseMetricExists_of_given <;> assumption)
