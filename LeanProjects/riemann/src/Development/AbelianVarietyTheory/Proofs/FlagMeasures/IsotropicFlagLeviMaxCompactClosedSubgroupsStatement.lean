import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsotropicFlagLeviMaxCompactClosedSubgroups
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.IsGaugeAll
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isotropicFlagLevi_maxCompact_closed_subgroups : ∀ (n : ℕ) (ε : Fin n → Bool) (a : ℕ) (W : Fin (a + 1) → Submodule ℂ (Fin n → ℂ)), (∃ M : Subgroup (Formalism.REAL.UJ ε), (M : Set (Formalism.REAL.UJ ε)) = flagM ε W) ∧ IsClosed (flagM ε W) ∧ (∃ K : Subgroup (Formalism.REAL.UJ ε), (K : Set (Formalism.REAL.UJ ε)) = maxK ε) ∧ IsClosed (maxK ε) ∧ ∀ m ∈ flagM ε W, ∀ u ∈ flagN ε W, m * u * m⁻¹ ∈ flagN ε W := by
  first | exact @GlobalTheory.FlagLeviGroup.levi_compact_subgroups | exact GlobalTheory.FlagLeviGroup.levi_compact_subgroups | (intros; apply GlobalTheory.FlagLeviGroup.levi_compact_subgroups <;> assumption)
