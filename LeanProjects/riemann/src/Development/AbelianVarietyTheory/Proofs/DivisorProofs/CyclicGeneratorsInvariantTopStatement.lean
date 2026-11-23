import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CyclicGeneratorsInvariantTop
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IotaScalarOne
open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps GlobalTheory.DetInv Matrix TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cyclic_generators_invariant_top : ∀ (k : Type) [Field k] [IsAlgClosed k] (n e N : ℕ) (t T : Matrix (Fin n) (Fin n) k) (h : Polynomial k), 0 < e → h.Monic → h.Separable → t * T = T * t → t ^ e = 0 → (∀ x, t *ᵥ x = 0 → ∃ y, x = t ^ (e - 1) *ᵥ y) → (∀ x, ∃ y, Polynomial.aeval T h *ᵥ x = t *ᵥ y) → T.charpoly = h ^ (e * N) → ∃ x : Fin N → Fin n → k, ∀ U : Submodule k (Fin n → k), (∀ i, x i ∈ U) → (∀ z ∈ U, t *ᵥ z ∈ U) → (∀ z ∈ U, T *ᵥ z ∈ U) → U = ⊤ := by
  first | exact @GlobalTheory.DetInv.exists_generators_of_charpoly_eq_pow | exact GlobalTheory.DetInv.exists_generators_of_charpoly_eq_pow | (intros; apply GlobalTheory.DetInv.exists_generators_of_charpoly_eq_pow <;> assumption)
