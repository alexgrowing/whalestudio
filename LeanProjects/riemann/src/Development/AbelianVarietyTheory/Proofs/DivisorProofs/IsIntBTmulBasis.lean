import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRootSelectionUnitaryRankOne

noncomputable section

open IsDedekindDomain
open scoped TensorProduct

namespace GlobalTheory.AdicSpan

def IsIntB (v : HeightOneSpectrum ℤ) {M : Type} [AddCommGroup M] [Module ℚ M] {κ : Type} (b : Module.Basis κ ℚ M)
    (y : v.adicCompletion ℚ ⊗[ℚ] M) : Prop :=
  ∀ i, (Algebra.TensorProduct.basis (v.adicCompletion ℚ) b).repr y i ∈ v.adicCompletionIntegers ℚ

theorem isIntB_zero (v : HeightOneSpectrum ℤ) {M : Type} [AddCommGroup M] [Module ℚ M] {κ : Type}
    (b : Module.Basis κ ℚ M) : IsIntB v b 0 := fun i => by simp [zero_mem]

theorem isIntB_tmul_basis (v : HeightOneSpectrum ℤ) {M : Type} [AddCommGroup M] [Module ℚ M] {κ : Type}
    (b : Module.Basis κ ℚ M) (j : κ) : IsIntB v b ((1 : v.adicCompletion ℚ) ⊗ₜ[ℚ] b j) := fun i => by
  classical
  rw [Algebra.TensorProduct.basis_repr_tmul, b.repr_self, Finsupp.smul_apply, Finsupp.mapRange_apply,
    Finsupp.single_apply]
  split_ifs <;> simp [zero_mem, one_mem]

end GlobalTheory.AdicSpan
