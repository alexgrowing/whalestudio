import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIotaScalarExactPair
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IotaScalarOne
open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps GlobalTheory.DetInv Matrix TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_iota_scalar_exact_pair : ∀ (C : Type) [Field C] (N : ℕ) (α β : Matrix (Fin N) (Fin N) C), α * β = 0 → β * α = 0 → (∀ x, α *ᵥ x = 0 → ∃ y, x = β *ᵥ y) → ∃ lam : C, lam ≠ 0 ∧ IotaScalar α β β.rank lam := by
  first | exact @GlobalTheory.DetInv.ScalarEx.exists_iotaScalar | exact GlobalTheory.DetInv.ScalarEx.exists_iotaScalar | (intros; apply GlobalTheory.DetInv.ScalarEx.exists_iotaScalar <;> assumption)
