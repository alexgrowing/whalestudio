import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FinrankCocycleExtensionLeOrderThreeRelationAdd
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MemTwInv
open GlobalTheory.HeckeFamilyMatrices.CocBound
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finrank_cocycleExtension_le_orderThreeRelation_add : ∀ {G : Type} [Group G] {E : Type} [AddCommGroup E] [Module ℂ E] (Γ : Subgroup G) (ρ : G → E →ₗ[ℂ] E) (s t : G), (∀ g h v, ρ (g * h) v = ρ h (ρ g v)) → (∀ v, ρ 1 v = v) → s ^ 2 = t ^ 3 → Subgroup.closure ({s, t} : Set G) = ⊤ → FiniteDimensional ℂ E → FiniteDimensional ℂ (relThree Γ ρ t) → FiniteDimensional ℂ (extn Γ ρ s) ∧ Module.finrank ℂ (extn Γ ρ s) ≤ Module.finrank ℂ (relThree Γ ρ t) + Module.finrank ℂ E := by
  first | exact @GlobalTheory.HeckeFamilyMatrices.CocBound.finrank_extn_le | exact GlobalTheory.HeckeFamilyMatrices.CocBound.finrank_extn_le | (intros; apply GlobalTheory.HeckeFamilyMatrices.CocBound.finrank_extn_le <;> assumption)
