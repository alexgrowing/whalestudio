import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FinrankCocyclesAddTwistedInvariantLeExtension
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MemTwInv
open GlobalTheory.HeckeFamilyMatrices.CocBound
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finrank_cocycles_add_twistedInvariant_le_extension : ∀ {G : Type} [Group G] {E : Type} [AddCommGroup E] [Module ℂ E] (Γ : Subgroup G) (ρ : G → E →ₗ[ℂ] E) (s : G), (∀ g h v, ρ (g * h) v = ρ h (ρ g v)) → (∀ v, ρ 1 v = v) → s ^ 4 = 1 → FiniteDimensional ℂ (extn Γ ρ s) → FiniteDimensional ℂ (cocyc Γ ρ) ∧ Module.finrank ℂ (cocyc Γ ρ) + Module.finrank ℂ (twInv Γ s (ρ s)) ≤ Module.finrank ℂ (extn Γ ρ s) := by
  first | exact @GlobalTheory.HeckeFamilyMatrices.CocBound.finrank_cocyc_add_twInv_le_extn | exact GlobalTheory.HeckeFamilyMatrices.CocBound.finrank_cocyc_add_twInv_le_extn | (intros; apply GlobalTheory.HeckeFamilyMatrices.CocBound.finrank_cocyc_add_twInv_le_extn <;> assumption)
