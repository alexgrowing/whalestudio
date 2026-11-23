import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.InducedProductCommutesFamilyProduct
import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.MultiProdCompCongr
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.SplitRead GlobalTheory.ProdReorder
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.inducedProductCommutes_familyProduct : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p u : ℕ) (x : Irr k p) (dτ : Fin (u + 1) → ℕ) (τ : ∀ a, Irr k (dτ a)), (∀ a, Commutes x (τ a)) → ∀ (T N : ℕ) (e : (Σ a, Fin (dτ a)) ≃ Fin T) (h₁ : p + T = N) (h₂ : T + p = N), Nonempty ((ind₂ (stdSum h₁) (extTensor x.π (multiProd e fun a => (τ a).π))).Equiv (ind₂ (stdSum h₂) (extTensor (multiProd e fun a => (τ a).π) x.π))) := by
  first | exact @GlobalTheory.ProdReorder.commutes_multiProd | exact GlobalTheory.ProdReorder.commutes_multiProd | (intros; apply GlobalTheory.ProdReorder.commutes_multiProd <;> assumption)
