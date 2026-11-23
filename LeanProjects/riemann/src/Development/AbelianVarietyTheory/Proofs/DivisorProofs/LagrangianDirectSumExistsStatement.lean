import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LagrangianDirectSumExists
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone

open scoped Matrix

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lagrangian_direct_sum_exists : ∀ {F : Type} [Field F] {κ : Type} [Fintype κ] (L₀ : Submodule F ((κ → F) × (κ → F))),
    (∀ a ∈ L₀, ∀ b ∈ L₀, a.1 ⬝ᵥ b.2 = b.1 ⬝ᵥ a.2) → Module.finrank F L₀ = Fintype.card κ →
    ∃ L : Submodule F ((κ ⊕ κ → F) × (κ ⊕ κ → F)), (∀ a ∈ L, ∀ b ∈ L, a.1 ⬝ᵥ b.2 = b.1 ⬝ᵥ a.2) ∧
      Module.finrank F L = Fintype.card (κ ⊕ κ) ∧
      ∀ w ∈ L, ∃ a ∈ L₀, ∃ b ∈ L₀, w = (Sum.elim a.1 b.1, Sum.elim a.2 (-b.2)) := by
  first | exact @GlobalTheory.lagrangian_doubling_exists | exact GlobalTheory.lagrangian_doubling_exists | (intros; apply GlobalTheory.lagrangian_doubling_exists <;> assumption)
