import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ChartLatticeDimensionUpper
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsNefSectionsAsymptotic
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsShiftSectionBound
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsFujitaOne
import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.Imports
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.KleimanNefness.AmpleSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ArithmeticHilbertSamuelLowerBound
import Development.AutomorphicSpectrum.PublishedTheorems.Geometry₂.NefRR
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.IsFieldSubalgebraSelf
import Development.WeilBound.CoreStatements.HodgeTatePoints.KTwins
import Development.WeilBound.CoreStatements.HodgeTatePoints.KleimanInputUniverseZero
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry GroundTheory.Heights₂.Heights.HilbertSamuel Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chart_lattice_dimension_upper : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [CharZero Ω] (y : (Σ k, ι k) → Ω) (D : ℕ) (a b : K → ℤ), 1 ≤ D → IsArithVar (mCoordIdeal y) (D + 1) → Birational y → NefOnGenericDeg (mCoordIdeal y) a → ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop, (Module.finrank ℚ (chartLatQ y ((n : ℤ) • a + b) 1) : ℝ) ≤ ((genDeg (mCoordIdeal y) D a : ℝ) + ε) * (n : ℝ) ^ D / (D.factorial : ℝ) := by
  first | exact @GlobalTheory.CompanionTheory.NefSections.finrank_chartLatQ_nsmul_add_le | exact GlobalTheory.CompanionTheory.NefSections.finrank_chartLatQ_nsmul_add_le | (intros; apply GlobalTheory.CompanionTheory.NefSections.finrank_chartLatQ_nsmul_add_le <;> assumption)
