import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IndexMeasureIntegralEqMeanOverRepresentatives
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Cint
open GlobalTheory.IdxInt
open scoped Pointwise Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.indexMeasureIntegral_eq_mean_over_representatives : ∀ {W : Type} [AddCommGroup W] (A B : AddSubgroup W) (φ : W → ℂ) (R : Finset W), B ≤ A → (∀ w, ∀ b ∈ B, φ (w + b) = φ w) → (∀ w, w ∉ A → φ w = 0) → (∀ w ∈ R, w ∈ A) → (∀ w ∈ A, ∃! x, x ∈ R ∧ w - x ∈ B) → Fine A φ B ∧ (R.card : ℕ) = B.relIndex A ∧ cint A φ = (∑ w ∈ R, φ w) / (R.card : ℂ) := by
  first | exact @GlobalTheory.IdxInt.cint_eq_mean_reps | exact GlobalTheory.IdxInt.cint_eq_mean_reps | (intros; apply GlobalTheory.IdxInt.cint_eq_mean_reps <;> assumption)
