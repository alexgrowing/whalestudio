import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DvrSubringEqTop
import Mathlib
open IsLocalRing
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.subring_eq_univ_of_uniformizer_generates : ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (S : Subring V) (π : V), π ∈ S → π ≠ 0 → π ∈ IsLocalRing.maximalIdeal V → (∀ s ∈ S, s ∉ IsLocalRing.maximalIdeal V → ∃ t ∈ S, s * t = 1) → (∀ s ∈ S, s ∈ IsLocalRing.maximalIdeal V → ∃ t ∈ S, s = π * t) → (∀ v : V, ∃ a ∈ S, ∃ b ∈ S, b ≠ 0 ∧ v * b = a) → S = ⊤ := by
  first | exact @GlobalTheory.dvrSubring_eq_top | exact GlobalTheory.dvrSubring_eq_top | (intros; apply GlobalTheory.dvrSubring_eq_top <;> assumption)
