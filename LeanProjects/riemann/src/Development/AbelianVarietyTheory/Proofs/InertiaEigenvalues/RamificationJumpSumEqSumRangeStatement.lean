import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RamificationJumpSumEqSumRange
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NoTowerQ
open Formalism.BasicNotions Formalism.BasicNotions.Loc ValuativeRel GroundTheory.LocalField GlobalTheory.PMon.Ram
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ramificationJumpSum_eq_sum_range : ∀ (G : Type) [Group G] (R : ℕ → Subgroup G) (A B : Subgroup G) (n : ℕ), Antitone R → (∀ t, t < n ↔ ¬ A ⊓ R t ≤ B) → jumpSum R A B = ∑ t ∈ Finset.range n, Nat.card ↥(A ⊓ R t) := by
  first | exact @GlobalTheory.PMon.Ram.jumpSum_eq_sum_range | exact GlobalTheory.PMon.Ram.jumpSum_eq_sum_range | (intros; apply GlobalTheory.PMon.Ram.jumpSum_eq_sum_range <;> assumption)
