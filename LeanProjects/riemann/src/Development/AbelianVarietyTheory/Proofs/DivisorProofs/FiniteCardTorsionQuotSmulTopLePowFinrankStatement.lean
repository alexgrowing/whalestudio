import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteCardTorsionQuotSmulTopLePowFinrank
import Mathlib
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_card_torsion_quot_smul_top_le_pow_finrank : ∀ (R : Type) [CommRing R] [IsDedekindDomain R] (M : Type) [AddCommGroup M] [Module R M] [Module.Finite R M] [Module.Projective R M] (I J : Ideal R), I.IsMaximal → Finite (R ⧸ I) → J ≠ ⊥ → Finite {y : M ⧸ J • (⊤ : Submodule R M) // ∀ a ∈ I, a • y = 0} ∧ Nat.card {y : M ⧸ J • (⊤ : Submodule R M) // ∀ a ∈ I, a • y = 0} ≤ Nat.card (R ⧸ I) ^ Module.finrank R M := by
  first | exact @GlobalTheory.TorsionCount.torsion_card | exact GlobalTheory.TorsionCount.torsion_card | (intros; apply GlobalTheory.TorsionCount.torsion_card <;> assumption)
