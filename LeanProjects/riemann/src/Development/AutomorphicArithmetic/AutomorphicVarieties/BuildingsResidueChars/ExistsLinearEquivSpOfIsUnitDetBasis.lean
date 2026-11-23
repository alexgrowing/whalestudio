import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GlobalUnitaryForms.HodgeTateFromSandwich
open UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Loc UpperTheory.V.Z.Sym.Glob Matrix

private theorem vecMul_of_three {R : Type} [CommRing R] (a b c : R) (e v w : Fin 3 → R) :
    ![a, b, c] ᵥ* (Matrix.of ![e, v, w]) = a • e + b • v + c • w := by
  ext j
  simp [Matrix.vecMul, dotProduct, Fin.sum_univ_three]

theorem UpperTheory.exists_linearEquiv_sp_of_isUnit_det_basis :
    ∀ (K : Type) [Field K] (Δ τ : K) (e v w : Fin 3 → Lsq K Δ), IsUnit (Matrix.of ![e, v, w]).det →
        ∃ P : Sp Δ τ ≃ₗ[Lsq K Δ] (Fin 3 → Lsq K Δ), ∀ x : Sp Δ τ, P x = x.1 • e + x.2.re • v + x.2.im • w := by
  intro K _ Δ τ e v w h
  set M : Matrix (Fin 3) (Fin 3) (Lsq K Δ) := Matrix.of ![e, v, w] with hM
  have h1 : M * M⁻¹ = 1 := Matrix.mul_nonsing_inv M h
  have h2 : M⁻¹ * M = 1 := Matrix.nonsing_inv_mul M h
  refine ⟨{ toFun := fun x => x.1 • e + x.2.re • v + x.2.im • w
            map_add' := ?_
            map_smul' := ?_
            invFun := fun y => ((y ᵥ* M⁻¹) 0, ⟨(y ᵥ* M⁻¹) 1, (y ᵥ* M⁻¹) 2⟩)
            left_inv := ?_
            right_inv := ?_ }, fun x => rfl⟩
  · intro x y
    simp only [Prod.fst_add, Prod.snd_add, QuadraticAlgebra.re_add, QuadraticAlgebra.im_add, add_smul]
    abel
  · intro r x
    simp [mul_smul, smul_add]
  · intro x
    have : (x.1 • e + x.2.re • v + x.2.im • w) ᵥ* M⁻¹ = ![x.1, x.2.re, x.2.im] := by
      rw [← vecMul_of_three, ← hM, Matrix.vecMul_vecMul, h1, Matrix.vecMul_one]
    simp only [this]
    ext <;> simp
  · intro y
    have : ((y ᵥ* M⁻¹) 0) • e + ((y ᵥ* M⁻¹) 1) • v + ((y ᵥ* M⁻¹) 2) • w = (y ᵥ* M⁻¹) ᵥ* M := by
      rw [hM, ← vecMul_of_three]
      congr 1
      funext i; fin_cases i <;> rfl
    simp only [this]
    rw [Matrix.vecMul_vecMul, h2, Matrix.vecMul_one]
