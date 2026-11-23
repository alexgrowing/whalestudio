import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDominatingDvrContainingFinset
import Mathlib
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_dominating_dvr_containing_finset : ∀ (F : Type) [Field F] [CharZero F] (T' : Subring F), IsDiscreteValuationRing T' → ∀ (s : Finset F), (1 : F) ∈ Submodule.span T' (s : Set F) → (∀ x ∈ s, ∀ y ∈ s, x * y ∈ Submodule.span T' (s : Set F)) → ∃ T'' : Subring F, IsDiscreteValuationRing T'' ∧ T' ≤ T'' ∧ (∀ x ∈ s, x ∈ T'') ∧ (∀ x ∈ T', (∃ y ∈ T'', x * y = 1) → ∃ y ∈ T', x * y = 1) ∧ (∀ y ∈ T'', ∃ d ∈ T', d ≠ 0 ∧ d * y ∈ Submodule.span T' (s : Set F)) := by
  first | exact @GlobalTheory.DomDVR.exists_dominating_dvr | exact GlobalTheory.DomDVR.exists_dominating_dvr | (intros; apply GlobalTheory.DomDVR.exists_dominating_dvr <;> assumption)
