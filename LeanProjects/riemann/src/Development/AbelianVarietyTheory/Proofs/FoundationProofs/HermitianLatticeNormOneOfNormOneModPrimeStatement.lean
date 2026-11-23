import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HermitianLatticeNormOneOfNormOneModPrime
import Mathlib
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermitianLattice_norm_one_of_norm_one_mod_prime : ∀ (K V : Type) [Field K] [CharZero K] [AddCommGroup V] [Module K V] (σ : K →+* K) (h : V →ₗ[K] V →ₛₗ[σ] K) (p d : ℕ) (θ : K) (O : Subring K) (L : AddSubgroup V), p.Prime → d.Prime → θ ^ 2 = -(d : K) → σ θ = -θ → (∀ x : K, ∃ a b : ℚ, x = (a : K) + (b : K) * θ) → (∀ x ∈ O, σ x ∈ O) → (1 + θ) / 2 ∈ O → (∀ r : ℚ, (r : K) ∈ O ↔ padicNorm p r ≤ 1) → (∀ x y : V, h y x = σ (h x y)) → (∀ x : V, h x x = 0 → x = 0) → (∀ a ∈ O, ∀ x ∈ L, a • x ∈ L) → (∀ x ∈ L, ∀ y ∈ L, h x y ∈ O) → (∀ x : V, ∃ m : ℕ, (p : K) ^ m • x ∈ L) → ∀ W : Submodule K V, (∃ e ∈ W, h e e = 1) → (∃ y ∈ L, y ∈ W ∧ ∃ u : ℚ, h y y = (u : K) ∧ padicNorm p (u - 1) < 1) → ∃ z ∈ L, z ∈ W ∧ h z z = 1 := by
  first | exact @GlobalTheory.exists_lattice_norm_one_of_norm_one_mod | exact GlobalTheory.exists_lattice_norm_one_of_norm_one_mod | (intros; apply GlobalTheory.exists_lattice_norm_one_of_norm_one_mod <;> assumption)
