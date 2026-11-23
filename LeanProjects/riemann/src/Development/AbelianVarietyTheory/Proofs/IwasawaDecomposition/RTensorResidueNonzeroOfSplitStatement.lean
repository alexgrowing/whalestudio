import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RTensorResidueNonzeroOfSplit
import Mathlib
import Development.AbelianVarietyTheory.Proofs.HermitianTraceForms.ExistsIsComplEigenSubOfValuationRing
open scoped TensorProduct NumberField
open GlobalTheory.EigenSplit

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rTensor_residue_nonzero_of_split : ∀ {O R k : Type} [CommRing O] [CommRing R] [IsLocalRing R] [Field k] [Module.Free ℤ O] [Module.Finite ℤ O]
    (ρ₀ : R →+* k), (∀ x, ρ₀ x = 0 → x ∈ IsLocalRing.maximalIdeal R) → ∀ (e : R ⊗[ℤ] O)
    (f : R ⊗[ℤ] O →ₗ[R] R), f e = 1 → ρ₀.toIntAlgHom.toLinearMap.rTensor O e ≠ 0 := by
  first | exact @GlobalTheory.rTensor_reduction_ne_zero_of_form_eq_one | exact GlobalTheory.rTensor_reduction_ne_zero_of_form_eq_one | (intros; apply GlobalTheory.rTensor_reduction_ne_zero_of_form_eq_one <;> assumption)
