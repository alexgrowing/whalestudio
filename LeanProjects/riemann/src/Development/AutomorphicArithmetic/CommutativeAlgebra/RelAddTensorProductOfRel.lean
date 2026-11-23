import Development.AutomorphicArithmetic.CommutativeAlgebra.ExistsEtaleTrivializationOfTwoInvertibleModuleTo

open CategoryTheory TensorProduct UpperTheory.PicD

private theorem cotangentAtUnit_tangentBijection {A C M M' : Type} [CommRing A] [CommRing C] [Algebra A C]
    [AddCommGroup M] [Module A M] [AddCommGroup M'] [Module A M']
    (t : M →ₗ[A] C) (t' : M' →ₗ[A] C)
    (h : Function.Bijective (LinearMap.liftBaseChange C t))
    (h' : Function.Bijective (LinearMap.liftBaseChange C t')) :
    Function.Bijective (LinearMap.liftBaseChange C
      ((Algebra.TensorProduct.lmul' A (S := C)).toLinearMap ∘ₗ TensorProduct.map t t')) := by
  let e := LinearEquiv.ofBijective _ h
  let e' := LinearEquiv.ofBijective _ h'
  let F : C ⊗[A] (M ⊗[A] M') ≃ₗ[C] C :=
    TensorProduct.AlgebraTensorModule.distribBaseChange A C M M' ≪≫ₗ TensorProduct.congr e e' ≪≫ₗ
      TensorProduct.lid C C
  have hF : ∀ x, F x = LinearMap.liftBaseChange C
      ((Algebra.TensorProduct.lmul' A (S := C)).toLinearMap ∘ₗ TensorProduct.map t t') x := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => rw [map_add, map_add, hx, hy]
    | tmul c y =>
      induction y using TensorProduct.induction_on with
      | zero => simp
      | add y1 y2 h1 h2 => rw [TensorProduct.tmul_add, map_add, map_add, h1, h2]
      | tmul m m' =>
        simp [F, e, e', LinearMap.liftBaseChange_tmul, smul_eq_mul, mul_assoc]
  have : ⇑(LinearMap.liftBaseChange C
      ((Algebra.TensorProduct.lmul' A (S := C)).toLinearMap ∘ₗ TensorProduct.map t t')) = F := by
    funext x
    exact (hF x).symm
  rw [this]
  exact F.bijective

theorem UpperTheory.rel_add_tensorProduct_of_rel :
    ∀ (P : Data) (A : Type) [CommRing A] (z z' : P.S1.obj (CommRingCat.of A)) (M M' : Type) [AddCommGroup M] [Module A M]
        [AddCommGroup M'] [Module A M'], P.Rel z M → P.Rel z' M' → P.Rel (z + z') (M ⊗[A] M') := by
  intro P A _ z z' M M' _ _ _ _ hz hz'
  obtain ⟨C, i1, i2, hff, het, w, g, t, w', g', t', T, T'⟩ := UpperTheory.exists_etale_trivialization_of_two_invertibleModuleTorsors P A z z' M M' hz hz'
  refine ⟨C, i1, i2, hff, het, w + w', g * g',
    (Algebra.TensorProduct.lmul' A (S := C)).toLinearMap ∘ₗ TensorProduct.map t t', ?_⟩
  refine ⟨?_, ?_, ?_, cotangentAtUnit_tangentBijection t t' T.bij T'.bij⟩
  · rw [map_add, map_add, T.dw, T'.dw]
  · rw [P.un_mul, T.hg, T'.hg, map_add, map_add]
    abel
  · intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => rw [map_add, add_smul, hx, hy, TensorProduct.tmul_add]
    | tmul m m' =>
      have h1 := T.ht m
      have h2 := T'.ht m'
      simp only [LinearMap.comp_apply, TensorProduct.map_tmul, AlgHom.toLinearMap_apply,
        Algebra.TensorProduct.lmul'_apply_tmul, Units.val_mul]
      rw [Algebra.smul_def] at h1 h2 ⊢
      rw [map_mul, show ∀ a b c d : C ⊗[A] C, a * b * (c * d) = (a * c) * (b * d) from
        fun a b c d => by ring, h1, h2, Algebra.TensorProduct.tmul_mul_tmul, one_mul]
