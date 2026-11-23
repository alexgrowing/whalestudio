import Mathlib
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.SaturatedLatticeQuotientCount
import Mathlib
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.saturated_lattice_quotient_count : ∀ (Λ : Type) [AddCommGroup Λ] [Module.Free ℤ Λ] [Module.Finite ℤ Λ] (B : LinearMap.BilinForm ℤ Λ), Function.Bijective B → (∀ x, B x x = 0) → ∀ W : Submodule ℤ Λ, (∀ (k : ℤ) x, k ≠ 0 → k • x ∈ W → x ∈ W) → (∀ N : ℕ, 0 < N → ∃ T : Set (W ⧸ LinearMap.range ((N : ℤ) • (LinearMap.id : W →ₗ[ℤ] W))), Nat.card (W ⧸ LinearMap.range ((N : ℤ) • (LinearMap.id : W →ₗ[ℤ] W))) * Nat.card T = N ^ Module.finrank ℤ Λ ∧ ∀ x y : W, Submodule.Quotient.mk x ∈ T → (N : ℤ) ∣ B x y) → ∀ x, (∀ y ∈ W, B x y = 0) → x ∈ W := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.mem_of_forall_card_mul_eq_pow | exact GlobalTheory.CompanionTheory.Ar.Flat.mem_of_forall_card_mul_eq_pow | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.mem_of_forall_card_mul_eq_pow <;> assumption)
