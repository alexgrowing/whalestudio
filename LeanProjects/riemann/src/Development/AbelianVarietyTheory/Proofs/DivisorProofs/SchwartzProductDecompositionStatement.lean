import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzProductDecomposition
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.schwartz_product_decomposition : ∀ (X : Type) [TopologicalSpace X] [LocallyCompactSpace X] [T2Space X] [TotallyDisconnectedSpace X]
    (κ κ' : Type) [Fintype κ] [Fintype κ'] (g : (κ ⊕ κ' → X) → ℂ), g ∈ GlobalTheory.WeilM.SB (κ ⊕ κ' → X) →
    ∃ (ι : Type) (_ : Fintype ι) (g₁ : ι → (κ → X) → ℂ) (g₂ : ι → (κ' → X) → ℂ),
      (∀ i, g₁ i ∈ GlobalTheory.WeilM.SB (κ → X)) ∧ (∀ i, g₂ i ∈ GlobalTheory.WeilM.SB (κ' → X)) ∧
      g = ∑ i, fun z => g₁ i (z ∘ Sum.inl) * g₂ i (z ∘ Sum.inr) := by
  first | exact @GlobalTheory.SBProd.exists_sum_box | exact GlobalTheory.SBProd.exists_sum_box | (intros; apply GlobalTheory.SBProd.exists_sum_box <;> assumption)
