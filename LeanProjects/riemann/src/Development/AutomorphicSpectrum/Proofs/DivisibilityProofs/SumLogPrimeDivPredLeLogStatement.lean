import Mathlib
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.SumLogPrimeDivPredLeLog
import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.PotentialsBoundedRegSettingEqReference
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BdryChart
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.IsPshLocallyIntegrableStatement
import Development.AutomorphicSpectrum.Statements.GeometryStatements.FlatDegree
import Development.AutomorphicSpectrum.Statements.GeometryStatements.NineGeoU
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sum_log_prime_div_pred_le_log : ∃ C : ℝ, 0 ≤ C ∧ ∀ (S S₀ : Finset ℕ) (B : ℕ), 2 ≤ B → (∀ p ∈ S, p.Prime ∧ (p ≤ B ∨ p ∈ S₀)) → S₀.card ≤ B → ∑ p ∈ S, Real.log (p : ℝ) / ((p : ℝ) - 1) ≤ C * Real.log B := by
  first | exact @GlobalTheory.CompanionTheory.Relay.sum_log_prime_div_pred_le_log | exact GlobalTheory.CompanionTheory.Relay.sum_log_prime_div_pred_le_log | (intros; apply GlobalTheory.CompanionTheory.Relay.sum_log_prime_div_pred_le_log <;> assumption)
