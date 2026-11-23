import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ComplexFlagAtEmbeddingFrameFinrankAndLowers
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LowersMulZero
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase GlobalTheory.RadCov
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.complexFlagAtEmbeddingFrame_finrank_and_lowers : ∀ (E : Type) [Field E] [NumberField E] (n : ℕ) (φ : E →+* ℂ) (P : Matrix (Fin n) (Fin n) ℂ) (F : ℕ → Submodule (𝓞 E) (Fin n → E)), IsUnit P → (∀ b, Module.finrank ℂ (locFlag φ P F b) = Formalism.HN.rkK (F b)) ∧ ∀ c, ∀ T ∈ lowers F c, P⁻¹ * T.map φ * P ∈ lowers (locFlag φ P F) c := by
  first | exact @GlobalTheory.RadCov.finrank_locFlag_and_lowers | exact GlobalTheory.RadCov.finrank_locFlag_and_lowers | (intros; apply GlobalTheory.RadCov.finrank_locFlag_and_lowers <;> assumption)
