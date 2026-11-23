import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NatCardQuotSmulTopLePowFinrank
import Mathlib
open NumberField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.natCard_quot_smul_le_pow_finrank : ∀ (E : Type) [Field E] [NumberField E] (La : Type) [AddCommGroup La] [Module (𝓞 E) La], Module.Finite (𝓞 E) La → Module.Projective (𝓞 E) La → ∀ (I : Ideal (𝓞 E)) (g : ℕ), g.Prime → Ideal.absNorm I = g → Finite (La ⧸ I • (⊤ : Submodule (𝓞 E) La)) ∧ Nat.card (La ⧸ I • (⊤ : Submodule (𝓞 E) La)) ≤ g ^ Module.finrank (𝓞 E) La := by
  first | exact @GlobalTheory.natCard_quot_smul_top_le_pow_finrank | exact GlobalTheory.natCard_quot_smul_top_le_pow_finrank | (intros; apply GlobalTheory.natCard_quot_smul_top_le_pow_finrank <;> assumption)
