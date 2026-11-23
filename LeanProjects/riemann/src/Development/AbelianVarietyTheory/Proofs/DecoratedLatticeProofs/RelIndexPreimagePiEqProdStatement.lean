import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RelIndexPreimagePiEqProd
import Mathlib
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.relIndex_eq_prod_relIndex_of_surjective_pi : ∀ {G : Type} [Group G] {r : ℕ} {H : Fin r → Type} [∀ i, Group (H i)] (φ : G →* ((i : Fin r) → H i)) (U U' : Subgroup G) (K J : (i : Fin r) → Subgroup (H i)), (∀ i, J i ≤ K i) → (∀ g ∈ U, ∀ i, φ g i ∈ K i) → (∀ x : (i : Fin r) → H i, (∀ i, x i ∈ K i) → ∃ g ∈ U, φ g = x) → (∀ g, g ∈ U' ↔ g ∈ U ∧ ∀ i, φ g i ∈ J i) → U'.relIndex U = ∏ i, (J i).relIndex (K i) := by
  first | exact @GlobalTheory.relIndex_preimage_pi_eq_prod | exact GlobalTheory.relIndex_preimage_pi_eq_prod | (intros; apply GlobalTheory.relIndex_preimage_pi_eq_prod <;> assumption)
