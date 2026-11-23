import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneLeNormMulPowIdeal
import Mathlib
open NumberField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.one_le_norm_mul_pow_ideal : ∀ (K : Type) [Field K] [NumberField K] (I J : Submodule (𝓞 K) K) (hI : I.FG) (hJ : J.FG) (i : ℕ), I ≠ ⊥ → J ≠ ⊥ → (∀ y ∈ I, ∀ b ∈ J, IsIntegral ℤ (b ^ i * y)) → 1 ≤ FractionalIdeal.absNorm (⟨I, FractionalIdeal.isFractional_of_fg hI⟩ : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) * FractionalIdeal.absNorm (⟨J, FractionalIdeal.isFractional_of_fg hJ⟩ : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) ^ i := by
  first | exact @GlobalTheory.one_le_absNorm_mul_absNorm_pow_of_forall_isIntegral | exact GlobalTheory.one_le_absNorm_mul_absNorm_pow_of_forall_isIntegral | (intros; apply GlobalTheory.one_le_absNorm_mul_absNorm_pow_of_forall_isIntegral <;> assumption)
