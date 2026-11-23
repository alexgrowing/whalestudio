import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IwasawaDecompositionUnitaryIsotropicFlag
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.IsGaugeAll
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.iwasawa_decomposition_unitary_isotropicFlag : ∀ (n : ℕ) (ε : Fin n → Bool) (a : ℕ) (j : Fin a → ℕ) (W : Fin (a + 1) → Submodule ℂ (Fin n → ℂ)), IsIsoFlag ε j W → (∀ g : Formalism.REAL.UJ ε, ∃ u ∈ flagN ε W, ∃ m ∈ flagM ε W, ∃ k ∈ maxK ε, g = u * m * k) ∧ ∀ u ∈ flagN ε W, ∀ m ∈ flagM ε W, u * m ∈ maxK ε → u = 1 := by
  first | exact @GlobalTheory.RealIwasawa.iwasawa | exact GlobalTheory.RealIwasawa.iwasawa | (intros; apply GlobalTheory.RealIwasawa.iwasawa <;> assumption)
