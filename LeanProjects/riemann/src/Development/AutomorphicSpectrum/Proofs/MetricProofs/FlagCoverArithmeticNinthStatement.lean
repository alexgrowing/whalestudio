import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagCoverArithmeticNinth
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Pull1
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsPeriodOn
import Development.AutomorphicSpectrum.Proofs.MetricProofs.IsImg
import GroundTheory.HeightsAndTheta.Heights.Intersections.PtsOverPt
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_arithVar_graph_of_flagCover : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (K' : Type) [Fintype K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)] (Φ' : Type) [Field Φ'] (y' : (Σ k, ι' k) → Φ') (M' : FlagModel y' Ψ N j) (Cv : FlagCover M' M) (d : ℕ), IsArithVar (mCoordIdeal y) (d + 2) → IsArithVar (mCoordIdeal y') (d + 2) → ∃ Pt : Ideal (MRing (Sum.elim ι ι')), IsArithVar Pt (d + 2) ∧ imageZ inlV Pt = mCoordIdeal y ∧ imageZ inrV Pt = mCoordIdeal y' ∧ ∀ z ∈ mcPts (mCoordIdeal y'), ∀ w ∈ mcPts (mCoordIdeal y), CovMap.IsImg Cv z w → ∃ zt ∈ mcPts Pt, (∀ p, zt (inlV p) = w p) ∧ ∀ q, zt (inrV q) = z q := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.CovGraph.graph_exists | exact GlobalTheory.CompanionTheory.Ar.PB.CovGraph.graph_exists | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.CovGraph.graph_exists <;> assumption)
