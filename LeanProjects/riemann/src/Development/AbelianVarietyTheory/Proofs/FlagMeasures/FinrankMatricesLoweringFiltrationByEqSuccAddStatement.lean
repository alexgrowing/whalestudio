import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FinrankMatricesLoweringFiltrationByEqSuccAdd
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LowersMulZero
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase GlobalTheory.RadCov
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finrank_matricesLoweringFiltrationBy_eq_succ_add : ∀ (n m : ℕ) (W : ℕ → Submodule ℂ (Fin n → ℂ)) (r : ℕ → ℕ) (U : ∀ b, Matrix (Fin n) (Fin (r b)) ℂ), Biorth r m U (fun b => (U b)ᴴ) → (∀ k y, y ∈ W k ↔ ∀ b, k ≤ b → (U b)ᴴ *ᵥ y = 0) → ∀ c, Module.finrank ℂ (lowers W c) = Module.finrank ℂ (lowers W (c + 1)) + ∑ b ∈ Finset.range m, r b * r (b + c + 1) := by
  first | exact @GlobalTheory.RadCov.finrank_lowers_eq_succ_add | exact GlobalTheory.RadCov.finrank_lowers_eq_succ_add | (intros; apply GlobalTheory.RadCov.finrank_lowers_eq_succ_add <;> assumption)
