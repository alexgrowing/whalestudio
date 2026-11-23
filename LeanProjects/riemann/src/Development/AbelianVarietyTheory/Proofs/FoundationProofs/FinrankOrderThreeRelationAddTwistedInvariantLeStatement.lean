import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FinrankOrderThreeRelationAddTwistedInvariantLe
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MemTwInv
open GlobalTheory.HeckeFamilyMatrices.CocBound
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finrank_orderThreeRelation_add_twistedInvariant_le : ∀ {G : Type} [Group G] {E : Type} [AddCommGroup E] [Module ℂ E] (Γ : Subgroup G) (ρ : G → E →ₗ[ℂ] E) (t : G), (∀ g h v, ρ (g * h) v = ρ h (ρ g v)) → (∀ v, ρ 1 v = v) → t ^ 6 = 1 → FiniteDimensional ℂ (twInv Γ (t ^ 3) (ρ (t ^ 3))) → FiniteDimensional ℂ (relThree Γ ρ t) ∧ Module.finrank ℂ (relThree Γ ρ t) + Module.finrank ℂ (twInv Γ t (ρ t)) ≤ Module.finrank ℂ (twInv Γ (t ^ 3) (ρ (t ^ 3))) := by
  first | exact @GlobalTheory.HeckeFamilyMatrices.CocBound.finrank_relThree_add_finrank_twInv_le | exact GlobalTheory.HeckeFamilyMatrices.CocBound.finrank_relThree_add_finrank_twInv_le | (intros; apply GlobalTheory.HeckeFamilyMatrices.CocBound.finrank_relThree_add_finrank_twInv_le <;> assumption)
