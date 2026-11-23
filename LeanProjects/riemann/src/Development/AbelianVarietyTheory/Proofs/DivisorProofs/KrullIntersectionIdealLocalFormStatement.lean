import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KrullIntersectionIdealLocalForm
import Mathlib
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.krull_intersection_ideal_local_form : ∀ (B : Type) [CommRing B] [IsNoetherianRing B] (I a a' : Ideal B), (∀ e : ℕ, a ≤ a' ⊔ I ^ (e + 1)) → ∃ r ∈ I, ∀ x ∈ a, (1 - r) * x ∈ a' := by
  first | exact @GlobalTheory.krull_inter_ideal_local | exact GlobalTheory.krull_inter_ideal_local | (intros; apply GlobalTheory.krull_inter_ideal_local <;> assumption)
