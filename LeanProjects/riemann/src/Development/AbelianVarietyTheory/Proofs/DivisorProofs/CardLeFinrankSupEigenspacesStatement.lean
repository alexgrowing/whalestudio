import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CardLeFinrankSupEigenspaces
import Mathlib
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.card_le_finrank_sup_eigenspaces : ∀ (W : Type 1) [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W] (O : Type) (T : O → Module.End ℂ W),
    (∀ a b, Commute (T a) (T b)) → ∀ (I : Type) [Fintype I] (ψ : I → O → ℂ), Function.Injective ψ →
    (∀ i, 1 ≤ Module.finrank ℂ (⨅ a, Module.End.eigenspace (T a) (ψ i a) : Submodule ℂ W)) →
    Fintype.card I ≤ Module.finrank ℂ (⨆ i, ⨅ a, Module.End.eigenspace (T a) (ψ i a) : Submodule ℂ W) := by
  first | exact @GlobalTheory.finrank_iSup_iInf_eigenspace_ge_card | exact GlobalTheory.finrank_iSup_iInf_eigenspace_ge_card | (intros; apply GlobalTheory.finrank_iSup_iInf_eigenspace_ge_card <;> assumption)
