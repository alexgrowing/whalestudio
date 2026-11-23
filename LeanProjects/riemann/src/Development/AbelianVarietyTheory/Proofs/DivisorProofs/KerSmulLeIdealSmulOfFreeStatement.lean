import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KerSmulLeIdealSmulOfFree
import Mathlib
open NumberField
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_span_smul_of_smul_eq_zero_of_free : ∀ (Λ : Type) [CommRing Λ] (t : Λ), (∀ x : Λ, t * x = 0 → x ∈ Ideal.span {t}) → ∀ (M : Type 1) [AddCommGroup M] [Module Λ M], Module.Free Λ M → ∀ m : M, t • m = 0 → m ∈ Ideal.span {t} • (⊤ : Submodule Λ M) := by
  first | exact @GlobalTheory.ker_smul_le_ideal_smul_of_free | exact GlobalTheory.ker_smul_le_ideal_smul_of_free | (intros; apply GlobalTheory.ker_smul_le_ideal_smul_of_free <;> assumption)
