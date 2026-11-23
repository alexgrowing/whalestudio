import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.BlockMatrixPlaces.BlockDiagonalOrdinaryGSpRep

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws UpperTheory.V.Ws.Bl

private theorem blk_one {R : Type} [CommRing R] : IsBlock (1 : M4 R) := fun i j h =>
  Matrix.one_apply_ne fun e => h (by rw [e])

private theorem key {R : Type} [CommRing R] {X Z Y : M4 R} (hX : IsBlock X) (hZ : Z ∈ hAB R) (hY : Y ∈ hAB R)
    (h : IsBlock ((1 - Y) * ((1 + Z) * X) * (1 + Y))) : Z * X + X * Y - Y * X = 0 := by
  have hZX : Z * X ∈ hAB R := by
    have h0 := hAB_mul_mul blk_one hZ hX
    rwa [one_mul] at h0
  have hXY : X * Y ∈ hAB R := by
    have h0 := hAB_mul_mul hX hY blk_one
    rwa [mul_one] at h0
  have hYX : Y * X ∈ hAB R := by
    have h0 := hAB_mul_mul blk_one hY hX
    rwa [one_mul] at h0
  have hN : Z * X + X * Y - Y * X ∈ hAB R := (hAB R).sub_mem ((hAB R).add_mem hZX hXY) hYX
  have h1 : ∀ W : M4 R, Y * (Z * W) = 0 := by
    intro W
    rw [← mul_assoc, hAB_mul_hAB hY hZ, zero_mul]
  have h2 : Y * (X * Y) = 0 := by rw [← mul_assoc, hAB_mul_hAB hYX hY]
  have h3 : Z * (X * Y) = 0 := by rw [← mul_assoc, hAB_mul_hAB hZX hY]
  have e : (1 - Y) * ((1 + Z) * X) * (1 + Y) = X + (Z * X + X * Y - Y * X) := by
    simp only [sub_mul, mul_sub, add_mul, mul_add, one_mul, mul_one, mul_assoc, h1, h2, h3, zero_mul, mul_zero]
    abel
  ext i j
  rw [Matrix.zero_apply]
  by_cases hij : lamW i = lamW j
  · exact hN i j (by rw [hij]; exact lt_irrefl _)
  · have hb := h i j hij
    rw [e, Matrix.add_apply, hX i j hij, zero_add] at hb
    exact hb

theorem UpperTheory.V.Ws.Bl.noCompl :
    ∀ (R Γ : Type) [CommRing R] [Group Γ] (r : Γ →* M4 R) (z : Γ → M4 R) (c : Γ) (Y : M4 R), IsUnit (2 : R) → (∀ g, IsBlock (r g)) → (∀ g, z g ∈ hAB R) → r c = eAB R → z c = 0 → Y ∈ hAB R →
          (∀ g, IsBlock ((1 - Y) * ((1 + z g) * r g) * (1 + Y))) → ∀ g, z g = 0 := by
  intro R Γ _ _ r z c Y h2u hrb hz hrc hzc hY hB g
  have hc := key (hrb c) (hz c) hY (hB c)
  rw [hzc, hrc, zero_mul, zero_add] at hc
  have hY0 : Y = 0 := by
    ext i j
    by_cases hij : lamW i < lamW j
    · have hd : (![-1, 1, -1, 1] : Fin 4 → R) i = 1 ∧ (![-1, 1, -1, 1] : Fin 4 → R) j = -1 := by
        fin_cases i <;> fin_cases j <;> simp [lamW] at hij ⊢
      have h2 : (2 : R) * Y i j = 0 := by
        have h0 := congrFun (congrFun hc i) j
        simp only [eAB, Matrix.sub_apply, Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.zero_apply] at h0
        rw [hd.1, hd.2] at h0
        linear_combination h0
      exact h2u.mul_right_eq_zero.mp h2
    · exact hY i j hij
  have hg := key (hrb g) (hz g) hY (hB g)
  rw [hY0, mul_zero, zero_mul, sub_zero, add_zero] at hg
  calc z g = z g * (r g * r g⁻¹) := by rw [← map_mul, mul_inv_cancel, map_one, mul_one]
    _ = 0 := by rw [← mul_assoc, hg, zero_mul]
