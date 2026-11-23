import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ParabolicProjectionToLevi
import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsStandardIndModule

open MeasureTheory Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagLeviGroup GlobalTheory.GKModule GlobalTheory.RealInd
open scoped InnerProductSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.parabolic_projection_to_levi : ∀ (n a : ℕ) (ε : Fin n → Bool) (j : Fin a → ℕ) (W : Flag n a), IsIsoFlag ε j W → (∀ i, 1 ≤ j i) →
    ∃ μ : UJ ε → UJ ε, ContinuousOn μ (parab ε W : Set (UJ ε)) ∧ (∀ p ∈ parab ε W, μ p ∈ leviOne ε W) ∧
      (∀ p ∈ parab ε W, ∀ q ∈ parab ε W, μ (p * q) = μ p * μ q) ∧
      ∀ u ∈ flagN ε W, ∀ m ∈ leviOne ε W, ∀ (x : Fin a → ℝ) (t : UJ ε), IsSplit ε W x t →
        u * m * t ∈ parab ε W ∧ μ (u * m * t) = m := by
  first | exact @GlobalTheory.LeviProj.exists_leviOne_part | exact GlobalTheory.LeviProj.exists_leviOne_part | (intros; apply GlobalTheory.LeviProj.exists_leviOne_part <;> assumption)
