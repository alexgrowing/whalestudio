import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDerivationEqOneOfPowMem
open TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_derivation_eq_one_of_pow_mem' : ∀ (p : ℕ) [Fact p.Prime] (K : Type) [Field K] [CharP K p] (L : Subfield K) (f : K), f ∉ L → f ^ p ∈ L → IntermediateField.adjoin L ({f} : Set K) = ⊤ → ∃ D : Derivation L K K, D f = 1 := by
  first | exact @GlobalTheory.exists_derivation_eq_one_of_pow_mem | exact GlobalTheory.exists_derivation_eq_one_of_pow_mem | (intros; apply GlobalTheory.exists_derivation_eq_one_of_pow_mem <;> assumption)
