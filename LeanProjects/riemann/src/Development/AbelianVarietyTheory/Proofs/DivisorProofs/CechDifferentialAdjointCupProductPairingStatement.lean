import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechDifferentialAdjointCupProductPairing
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DlogRatioVolumeFormNeZero
open GlobalTheory.PD GlobalTheory.CechDR KaehlerDifferential
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cechDifferential_adjoint_cupProductPairing : ∀ (k : Type) [Field k] (d : ℕ) (E : Type) [AddCommGroup E] [Module k E] (E' : Type) [AddCommGroup E'] [Module k E'] (A : Finset (Fin (d + 1)) → Submodule k E) (B : Finset (Fin (d + 1)) → Submodule k E') (β : E →ₗ[k] E' →ₗ[k] k), (∀ s t, s.Nonempty → s ⊆ t → A s ≤ A t) → (∀ s t, s.Nonempty → s ⊆ t → B s ≤ B t) → (∀ i, (Finset.univ.erase i).Nonempty → ∀ a ∈ A (Finset.univ.erase i), ∀ b ∈ B (Finset.univ.erase i), β a b = 0) → Adj (cech A) (cech B) (cupPair β) d := by
  first | (exact @GlobalTheory.PD.CupAdj.cech_adj) | (exact GlobalTheory.PD.CupAdj.cech_adj) | (intros; apply GlobalTheory.PD.CupAdj.cech_adj  <;> assumption)
