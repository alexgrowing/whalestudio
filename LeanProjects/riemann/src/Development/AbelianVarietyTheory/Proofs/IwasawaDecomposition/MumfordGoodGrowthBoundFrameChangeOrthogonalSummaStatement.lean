import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MumfordGoodGrowthBoundFrameChangeOrthogonalSumma
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsLieBase
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.HodgePeriodGram
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HodgeChartBoundsOfSchurLemW
open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open Matrix
open scoped ComplexOrder Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mumfordGoodGrowthBound_frameChange_orthogonalSummands : ∀ (n g : ℕ) (S : Finset (Fin n)) (W : Set (ReciprocityTheory.L2DbarEstimates.V n)) (G₀ : ReciprocityTheory.L2DbarEstimates.V n → Matrix (Fin g) (Fin g) ℂ) (c : ℝ) (N : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] (m : ι → ℕ) (Q : ∀ τ : ι, ReciprocityTheory.L2DbarEstimates.V n → Matrix (Fin (m τ)) (Fin g) ℂ) (r : ℝ), IsOpen W → 0 < r → (∀ τ i k, DifferentiableOn ℂ (fun u => Q τ u i k) (Metric.ball 0 r)) → Fintype.card (Σ τ, Fin (m τ)) = g → LinearIndependent ℂ (fun p : Σ τ, Fin (m τ) => Q p.1 0 p.2) → (∀ v ∈ W, (G₀ v).det ≠ 0 ∧ (∀ i k, ContDiffAt ℝ 2 (fun u => G₀ u i k) v) ∧ GlobalTheory.GoodMetric.GoodBound S c N G₀ v) → (∀ v ∈ W, ∀ τ τ', τ ≠ τ' → Q τ v * G₀ v * (Q τ' v)ᴴ = 0) → ∃ r' : ℝ, 0 < r' ∧ ∃ (c' : ℝ) (N' : ℕ), ∀ v ∈ W, ‖v‖ < r' → ∀ τ, GlobalTheory.GoodMetric.GoodBound S c' N' (fun u => Q τ u * G₀ u * (Q τ u)ᴴ) v := by
  first | exact @GlobalTheory.FrameGood.frame_summands_goodBound | exact GlobalTheory.FrameGood.frame_summands_goodBound | (intros; apply GlobalTheory.FrameGood.frame_summands_goodBound <;> assumption)
