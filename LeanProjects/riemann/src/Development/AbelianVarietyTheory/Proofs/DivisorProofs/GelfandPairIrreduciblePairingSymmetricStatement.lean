import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GelfandPairIrreduciblePairingSymmetric
import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DixmierCommutantScalar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gelfand_pair_irreducible_pairing_symmetric : ∀ (G : Type) [Group G] (K : Subgroup G), (∀ g : G, (K.map (MulAut.conj g).toMonoidHom).relIndex K ≠ 0) →
    ∀ θ : G → G, (∀ x y, θ (x * y) = θ y * θ x) → (∀ x, θ (θ x) = x) → (∀ g, ∃ a ∈ K, ∃ b ∈ K, θ g = a * g * b) →
    ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V), Module.rank ℂ V ≤ Cardinal.aleph0 →
    (∀ N : Submodule ℂ V, (∀ g, ∀ x ∈ N, ρ g x ∈ N) → N = ⊥ ∨ N = ⊤) →
    ∀ x y : V, (∀ k ∈ K, ρ k x = x) → (∀ k ∈ K, ρ k y = y) → x ≠ 0 → ∃ c : ℂ, y = c • x := by
  first | exact @GlobalTheory.fixed_line_of_gelfand_countable | exact GlobalTheory.fixed_line_of_gelfand_countable | (intros; apply GlobalTheory.fixed_line_of_gelfand_countable <;> assumption)
