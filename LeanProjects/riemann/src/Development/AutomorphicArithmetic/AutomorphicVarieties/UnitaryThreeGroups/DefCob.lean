import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.BaseRepGL3NormalisedOfPsiEqOne

open Matrix UpperTheory.V.U3

private theorem UpperTheory.V.U3.defcob_mul_zero {C : Type} [CommRing C] {m : ℕ} {I : Ideal C}
    (hI : I * I = ⊥) {X Y : Matrix (Fin m) (Fin m) C} (hX : EntIn I X) (hY : EntIn I Y)
    (A : Matrix (Fin m) (Fin m) C) : X * A * Y = 0 := by
  ext i j
  rw [Matrix.mul_apply, Matrix.zero_apply]
  refine Finset.sum_eq_zero fun k _ => ?_
  have h1 : (X * A) i k ∈ I := by
    rw [Matrix.mul_apply]
    exact I.sum_mem fun l _ => I.mul_mem_right _ (hX i l)
  have h2 := Ideal.mul_mem_mul h1 (hY k j)
  rw [hI] at h2
  exact h2

private theorem UpperTheory.V.U3.defcob_entIn {C : Type} [CommRing C] {m : ℕ} {I : Ideal C}
    {X : Matrix (Fin m) (Fin m) C} (hX : EntIn I X)
    (A B : Matrix (Fin m) (Fin m) C) : EntIn I (A * Xᵀ * B) := by
  intro i j
  rw [Matrix.mul_apply]
  refine I.sum_mem fun k _ => I.mul_mem_right _ ?_
  rw [Matrix.mul_apply]
  exact I.sum_mem fun l _ => I.mul_mem_left _ (hX k l)

theorem UpperTheory.V.U3.isDeform_cob :
    ∀ {G C : Type} [Group G] [CommRing C] {m : ℕ} (I : Ideal C) (r : G →* GG m C) (X : Matrix (Fin m) (Fin m) C), I * I = ⊥ → EntIn I X →
      ∃ h : GL (Fin m) C, (h : Matrix (Fin m) (Fin m) C) = 1 + X ∧ IsDeform r (cob r X) (conjBy h r) := by
  intro G C _ _ m I r X hI hX
  have hXX : X * X = 0 := by simpa using defcob_mul_zero hI hX hX 1
  let h : GL (Fin m) C := ⟨1 + X, 1 - X, by
    rw [Matrix.mul_sub, Matrix.add_mul, Matrix.add_mul, hXX]; simp, by
    rw [Matrix.mul_add, Matrix.sub_mul, Matrix.sub_mul, hXX]; simp⟩
  have hv : (h : Matrix (Fin m) (Fin m) C) = 1 + X := rfl
  have hi : ((h⁻¹ : GL (Fin m) C) : Matrix (Fin m) (Fin m) C) = 1 - X := rfl
  refine ⟨h, rfl, fun g => ⟨by simp [conjBy], ?_⟩⟩
  have hl : (conjBy h r g).mat = (1 + X) * (r g).mat *
      ((sgnAct m C (r g).right h⁻¹ : GL (Fin m) C) : Matrix (Fin m) (Fin m) C) := by
    simp [conjBy, GG.mat, hv]
  have hc : cob r X g = X - (r g).adFun X := rfl
  have ha : (((r g).left⁻¹ : GL (Fin m) C) : Matrix (Fin m) (Fin m) C) * (r g).mat = 1 :=
    Units.inv_mul _
  rw [hl, hc, GG.adFun]
  rcases Int.units_eq_one_or (r g).right with hs | hs
  · rw [hs, sgnAct_one, hi, if_pos rfl]
    simp only [Matrix.mul_sub, Matrix.add_mul, Matrix.sub_mul, Matrix.one_mul, Matrix.mul_one]
    rw [defcob_mul_zero hI hX hX, Matrix.mul_assoc _ _ (r g).mat, ha, Matrix.mul_one]
    abel
  · have hJ : Jmat C m * (1 + X)ᵀ * Jmat C m = 1 + Jmat C m * Xᵀ * Jmat C m := by
      rw [Matrix.transpose_add, Matrix.transpose_one, Matrix.mul_add, Matrix.add_mul,
        Matrix.mul_one, Jmat_mul_Jmat]
    rw [hs, sgnAct_neg_one, theta_val, inv_inv, hv, hJ, if_neg (by decide), thetaLie]
    simp only [Matrix.mul_add, Matrix.add_mul, Matrix.sub_mul, Matrix.one_mul, Matrix.mul_one]
    rw [defcob_mul_zero hI hX (defcob_entIn hX _ _), Matrix.mul_assoc _ _ (r g).mat, ha,
      Matrix.mul_one, Matrix.mul_neg]
    abel
