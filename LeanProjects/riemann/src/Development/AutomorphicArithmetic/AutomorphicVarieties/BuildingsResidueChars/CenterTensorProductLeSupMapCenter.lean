import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.CuspidalFiniteness.HasUnivOfStep
import Mathlib.Algebra.Algebra.Subalgebra.Centralizer

theorem UpperTheory.center_tensorProduct_le_sup_map_center :
    ∀ (A B : Type) [Ring A] [Algebra ℂ A] [Ring B] [Algebra ℂ B], Subalgebra.center ℂ (TensorProduct ℂ A B) ≤ (Subalgebra.center ℂ A).map (Algebra.TensorProduct.includeLeft : A →ₐ[ℂ] TensorProduct ℂ A B) ⊔ (Subalgebra.center ℂ B).map (Algebra.TensorProduct.includeRight : B →ₐ[ℂ] TensorProduct ℂ A B) := by
  intro A B _ _ _ _ z hz
  have hz' := Subalgebra.mem_center_iff.1 hz
  have h1 : z ∈ Subalgebra.centralizer ℂ
      ((Algebra.TensorProduct.includeLeft : A →ₐ[ℂ] TensorProduct ℂ A B).range :
        Set (TensorProduct ℂ A B)) := by
    rw [Subalgebra.mem_centralizer_iff]
    intro g _
    exact hz' g
  rw [Subalgebra.centralizer_coe_range_includeLeft_eq_center_tensorProduct] at h1
  obtain ⟨w, hw⟩ := h1
  have hw' : Algebra.TensorProduct.map (Subalgebra.center ℂ A).val (AlgHom.id ℂ B) w = z := hw
  have hinj : Function.Injective
      (Algebra.TensorProduct.map (Subalgebra.center ℂ A).val (AlgHom.id ℂ B)) := by
    have h := Module.Flat.rTensor_preserves_injective_linearMap (R := ℂ) (M := B)
      (Subalgebra.center ℂ A).val.toLinearMap Subtype.val_injective
    exact h
  have h2 : w ∈ Subalgebra.centralizer ℂ
      ((Algebra.TensorProduct.includeRight :
        B →ₐ[ℂ] TensorProduct ℂ (Subalgebra.center ℂ A) B).range :
        Set (TensorProduct ℂ (Subalgebra.center ℂ A) B)) := by
    rw [Subalgebra.mem_centralizer_iff]
    intro g _
    apply hinj
    rw [map_mul, map_mul, hw']
    exact hz' _
  rw [Subalgebra.centralizer_range_includeRight_eq_center_tensorProduct] at h2
  obtain ⟨v, hv⟩ := h2
  have hv' : Algebra.TensorProduct.map (AlgHom.id ℂ (Subalgebra.center ℂ A))
      (Subalgebra.center ℂ B).val v = w := hv
  rw [← hw', ← hv']
  clear hv' hv hw' hw hz' hz
  induction v using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero]; exact Subalgebra.zero_mem _
  | add x y hx hy => rw [map_add, map_add]; exact Subalgebra.add_mem _ hx hy
  | tmul a b =>
    have e : Algebra.TensorProduct.map (Subalgebra.center ℂ A).val (AlgHom.id ℂ B)
        (Algebra.TensorProduct.map (AlgHom.id ℂ (Subalgebra.center ℂ A))
          (Subalgebra.center ℂ B).val (a ⊗ₜ[ℂ] b)) =
        (Algebra.TensorProduct.includeLeft : A →ₐ[ℂ] TensorProduct ℂ A B) (a : A) *
        (Algebra.TensorProduct.includeRight : B →ₐ[ℂ] TensorProduct ℂ A B) (b : B) := by
      simp
    rw [e]
    exact Algebra.mul_mem_sup ⟨a, a.2, rfl⟩ ⟨b, b.2, rfl⟩
