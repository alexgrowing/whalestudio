import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MumfordGoodGrowthBoundHolomorphicFrameChange
import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsLieBase
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.HodgePeriodGram
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HodgeChartBoundsOfSchurLemW
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OpNormLeOpNormBlockDiagonal
open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open Matrix
open scoped ComplexOrder Topology

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mumfordGoodGrowthBound_holomorphic_frameChange : ∀ (n : ℕ) (K : Type) [Fintype K] [DecidableEq K] (S : Finset (Fin n)) (c : ℝ) (N : ℕ) (B : ℝ), ∃ c' : ℝ, ∀ (G₀ P : ReciprocityTheory.L2DbarEstimates.V n → Matrix K K ℂ) (v : ReciprocityTheory.L2DbarEstimates.V n), ‖v‖ < 1 → (G₀ v).det ≠ 0 → (∀ i k, ContDiffAt ℝ 2 (fun u => G₀ u i k) v) → (∀ i k, ContDiffAt ℝ 2 (fun u => P u i k) v) → (∀ᶠ u in nhds v, ∀ η, GlobalTheory.HermFrame.mdbar P u η = 0) → IsUnit (P v).det → (∀ i k, ‖P v i k‖ ≤ B) → (∀ i k, ‖(P v)⁻¹ i k‖ ≤ B) → (∀ a i k, ‖GlobalTheory.HermFrame.mdel P v (GlobalTheory.GoodMetric.coordVec a) i k‖ ≤ B) → (∀ a b i k, ‖GlobalTheory.HermFrame.mdel (fun u => GlobalTheory.HermFrame.mdel P u (GlobalTheory.GoodMetric.coordVec b)) v (GlobalTheory.GoodMetric.coordVec a) i k‖ ≤ B) → GlobalTheory.GoodMetric.GoodBound S c N G₀ v → (P v * G₀ v * (P v)ᴴ).det ≠ 0 ∧ (∀ i k, ContDiffAt ℝ 2 (fun u => (P u * G₀ u * (P u)ᴴ) i k) v) ∧ GlobalTheory.GoodMetric.GoodBound S c' N (fun u => P u * G₀ u * (P u)ᴴ) v := by
  first | exact @GlobalTheory.GoodMetric.FrameChange.goodBound_changeFrame | exact GlobalTheory.GoodMetric.FrameChange.goodBound_changeFrame | (intros; apply GlobalTheory.GoodMetric.FrameChange.goodBound_changeFrame <;> assumption)
