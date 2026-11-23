import Mathlib

open scoped TensorProduct

namespace GlobalTheory.OneTensorSpanTop

theorem span_one_tmul_eq_top (k : Type) [Field k] (C O : Type) [CommRing C] [Ring O]
    [Algebra C O] [Algebra C k] :
    Submodule.span k (Set.range fun (o : O) ↦ (1 : k) ⊗ₜ[C] o) = ⊤ := by
  rw [eq_top_iff]
  rintro x -
  induction x using TensorProduct.induction_on with
  | zero => exact Submodule.zero_mem _
  | tmul a o =>
    have h : a ⊗ₜ[C] o = a • ((1 : k) ⊗ₜ[C] o) := by
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    rw [h]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨o, rfl⟩)
  | add x y hx hy => exact Submodule.add_mem _ hx hy

end GlobalTheory.OneTensorSpanTop
