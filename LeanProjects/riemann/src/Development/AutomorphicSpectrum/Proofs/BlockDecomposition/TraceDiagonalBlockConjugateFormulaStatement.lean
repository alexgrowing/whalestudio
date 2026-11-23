import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TraceDiagonalBlockConjugateFormula
import Development.WeilBound.RepresentationTheoryGL.HolomorphicDiscreteSeries.EmbeddedFrames.PfD
import Formalism.RealPlaceAnalysis.Complexify
open Finset Matrix PositivityTheory.RgHe.Frame
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.trace_diagonal_block_conjugate_formula : ∀ (n : ℕ) (e : Fin n ⊕ Unit ≃ Fin (n + 1)) (d : Fin (n + 1) → ℝ) (d' : Fin n → ℝ) (g X : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ), IsUnit g.det → X * g = g * diagonal (fun i => ((d i : ℝ) : ℂ)) → (∀ a b, X (e (Sum.inl a)) (e (Sum.inl b)) = if a = b then ((d' a : ℝ) : ℂ) else 0) → ∀ Y : Matrix (Fin n) (Fin n) ℂ, trace (diagonal (fun i => ((d i : ℝ) : ℂ)) * (g⁻¹ * Matrix.reindex e e (Matrix.fromBlocks Y 0 0 0) * g)) = trace (diagonal (fun a => ((d' a : ℝ) : ℂ)) * Y) := by
  first | exact @GlobalTheory.CompanionTheory.RgHeFrame.trace_diagonal_block_conjugate | exact GlobalTheory.CompanionTheory.RgHeFrame.trace_diagonal_block_conjugate | (intros; apply GlobalTheory.CompanionTheory.RgHeFrame.trace_diagonal_block_conjugate <;> assumption)
