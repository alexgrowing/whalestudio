import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MollificationRightTranslate
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RwAppend
open MeasureTheory Matrix Finset Filter Topology
open scoped ContDiff ComplexConjugate InnerProductSpace ZeroAtInfty
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Fc GlobalTheory.CompanionTheory.PresSobA
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
noncomputable section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mollification_right_translate : ∀ (n : ℕ) [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n)) [μ.IsHaarMeasure] (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V], Unimod → ∀ (φ : Mat n → ℝ) (h : G n) (x : Lp V 2 μ) (z : Mat n), Mol μ φ (⇑(rR μ V h x)) z = Mol μ φ (⇑x) (z * h.val) := by
  first | exact @GlobalTheory.CompanionTheory.PresSobA.Mol_rR_eq | exact GlobalTheory.CompanionTheory.PresSobA.Mol_rR_eq | (intros; apply GlobalTheory.CompanionTheory.PresSobA.Mol_rR_eq <;> assumption)
