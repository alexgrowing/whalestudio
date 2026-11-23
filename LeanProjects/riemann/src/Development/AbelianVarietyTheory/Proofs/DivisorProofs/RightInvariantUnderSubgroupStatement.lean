import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RightInvariantUnderSubgroup
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThLiftMemLiftSpace
open GlobalTheory.ThK.SplitInv
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.right_invariant_under_subgroup : ∀ (H : Type) [Group H] (G₀ : Subgroup H) (S : Submodule ℂ (H → ℂ)), RStable G₀ S → CompRed G₀ S → QuotTriv G₀ S → ∀ φ ∈ S, ∀ k ∈ G₀, ∀ g, φ (g * k) = φ g := by
  first | exact @GlobalTheory.ThK.SplitInv.TrivQuot.invariant_of_compRed_quotTriv | exact GlobalTheory.ThK.SplitInv.TrivQuot.invariant_of_compRed_quotTriv | (intros; apply GlobalTheory.ThK.SplitInv.TrivQuot.invariant_of_compRed_quotTriv <;> assumption)
