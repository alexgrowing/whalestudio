import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.InterlacingSignatureParity
import Development.WeilBound.RepresentationTheoryGL.HolomorphicDiscreteSeries.EmbeddedFrames.PfD
import Formalism.RealPlaceAnalysis.Complexify
import Development.WeilBound.CoreStatements.BranchingTraces.HeBranching
open Finset Matrix PositivityTheory.RgHe.Frame
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.interlacing_signature_parity : ∀ (n : ℕ) (ε : Fin (n + 1) → Bool) (d : Fin (n + 1) → ℝ) (ε' : Fin n → Bool) (d' : Fin n → ℝ) (e : Fin n ⊕ Unit ≃ Fin (n + 1)), PositivityTheory.UnitaryDecomposition.Fits ε ε' e → Function.Injective (Sum.elim d d') → PositivityTheory.UnitaryDecomposition.HeWord ε d ε' d' → (∀ i, (ε i = true ↔ Even (above d d' (d i)))) ∧ ∀ j, (ε' j = true ↔ ¬ Even (above d d' (d' j))) := by
  first | exact @GlobalTheory.CompanionTheory.RgHeFrame.SignWord.heSign | exact GlobalTheory.CompanionTheory.RgHeFrame.SignWord.heSign | (intros; apply GlobalTheory.CompanionTheory.RgHeFrame.SignWord.heSign <;> assumption)
