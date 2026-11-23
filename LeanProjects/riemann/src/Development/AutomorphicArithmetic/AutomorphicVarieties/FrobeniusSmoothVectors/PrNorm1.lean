import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.PresDefs

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

theorem UpperTheory.V.Fr.pr_norm1 :
    ∀ (O : Type) [CommRing O] [IsLocalRing O], ∀ (C' : Type) [CommRing C'] [Algebra O C'] [IsCO O C'] (C : Type) [CommRing C] [Algebra O C] (p : C' →ₐ[O] C) (n : ℕ) (x : GG n C'), maximalIdeal C' * RingHom.ker p = ⊥ → RingHom.ker p ≤ maximalIdeal C' → (2 : ResidueField O) ≠ 0 → x * x = 1 → x.right = -1 → x.mat.map p = 1 → ∃ h : GL (Fin n) C', (h : Matrix (Fin n) (Fin n) C').map p = 1 ∧ (GG.ofGL h * x * (GG.ofGL h)⁻¹).mat = 1 := by
  intro O _ _ C' _ _ _ C _ _ p n x hmI hle h2R hxx hr hmap
  have hgt : x.left * theta x.left = 1 := by
    have hl := congrArg SemidirectProduct.left hxx
    simpa [SemidirectProduct.mul_left, hr] using hl
  have hθ : ∀ u : GL (Fin n) C', ((theta u⁻¹ : GL (Fin n) C') : Matrix (Fin n) (Fin n) C') =
      Jmat C' n * (u : Matrix (Fin n) (Fin n) C')ᵀ * Jmat C' n := by
    intro u
    rw [show theta u⁻¹ = (theta u)⁻¹ from map_inv (thetaAut n C') u, theta_inv_val]
  have hgg : (x.left : Matrix (Fin n) (Fin n) C') =
      Jmat C' n * (x.left : Matrix (Fin n) (Fin n) C')ᵀ * Jmat C' n := by
    have h1 : (theta x.left)⁻¹ = x.left := inv_eq_of_mul_eq_one_left hgt
    rw [← theta_inv_val x.left, h1]
  have hsq : ∀ a b : C', a ∈ RingHom.ker p → b ∈ RingHom.ker p → a * b = 0 := by
    intro a b ha hb
    have hab : a * b ∈ maximalIdeal C' * RingHom.ker p := Ideal.mul_mem_mul (hle ha) hb
    rw [hmI] at hab
    exact (Ideal.mem_bot).mp hab
  have hp1 : ∀ i j : Fin n,
      p ((1 : Matrix (Fin n) (Fin n) C') i j) = (1 : Matrix (Fin n) (Fin n) C) i j := by
    intro i j
    rw [Matrix.one_apply, Matrix.one_apply]
    split_ifs <;> simp
  set X : Matrix (Fin n) (Fin n) C' := (x.left : Matrix (Fin n) (Fin n) C') - 1 with hXdef
  have hX : ∀ i j, X i j ∈ RingHom.ker p := by
    intro i j
    have hgij : p ((x.left : Matrix (Fin n) (Fin n) C') i j) = (1 : Matrix (Fin n) (Fin n) C) i j :=
      congrFun (congrFun hmap i) j
    rw [RingHom.mem_ker, hXdef, Matrix.sub_apply, map_sub, hp1, hgij, sub_self]
  have hXX : X * X = 0 := by
    ext i j
    rw [Matrix.mul_apply, Matrix.zero_apply]
    exact Finset.sum_eq_zero fun k _ => hsq _ _ (hX i k) (hX k j)
  have hXJ : Jmat C' n * Xᵀ * Jmat C' n = X := by
    rw [hXdef, Matrix.transpose_sub, Matrix.transpose_one, Matrix.mul_sub, Matrix.sub_mul,
      Matrix.mul_one, Jmat_mul_Jmat, ← hgg]
  have hO : IsUnit (2 : O) := by
    rw [← IsLocalRing.notMem_maximalIdeal, ← IsLocalRing.residue_eq_zero_iff, map_ofNat]
    exact h2R
  have h2 : IsUnit (2 : C') := by
    have h2' := hO.map (algebraMap O C')
    rwa [map_ofNat] at h2'
  have hc2 : (↑h2.unit⁻¹ : C') * 2 = 1 := h2.val_inv_mul
  set Y : Matrix (Fin n) (Fin n) C' := (↑h2.unit⁻¹ : C') • X with hYdef
  have hYX : Y * X = 0 := by rw [hYdef, Matrix.smul_mul, hXX, smul_zero]
  have hXY : X * Y = 0 := by rw [hYdef, Matrix.mul_smul, hXX, smul_zero]
  have hYY : Y * Y = 0 := by rw [hYdef, Matrix.mul_smul, hYX, smul_zero]
  have hY2 : Y + Y = X := by rw [hYdef, ← add_smul, ← mul_two, hc2, one_smul]
  have e1 : (1 - Y) * (1 + Y) = 1 := by
    rw [sub_mul, one_mul, mul_add, mul_one, hYY, add_zero, add_sub_cancel_right]
  have e2 : (1 + Y) * (1 - Y) = 1 := by
    rw [add_mul, one_mul, mul_sub, mul_one, hYY, sub_zero, sub_add_cancel]
  have hpY : ∀ i j, p (Y i j) = 0 := by
    intro i j
    rw [hYdef, Matrix.smul_apply, smul_eq_mul, map_mul, (RingHom.mem_ker).mp (hX i j), mul_zero]
  obtain ⟨U, hU⟩ : ∃ U : GL (Fin n) C', (U : Matrix (Fin n) (Fin n) C') = 1 - Y :=
    ⟨⟨1 - Y, 1 + Y, e1, e2⟩, rfl⟩
  have hJ : Jmat C' n * (1 - Y)ᵀ * Jmat C' n = 1 - Y := by
    rw [Matrix.transpose_sub, Matrix.transpose_one, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one,
      Jmat_mul_Jmat, hYdef, Matrix.transpose_smul, Matrix.mul_smul, Matrix.smul_mul, hXJ]
  have hg1 : (x.left : Matrix (Fin n) (Fin n) C') = 1 + X := by rw [hXdef, add_sub_cancel]
  have key : (1 - Y) * (1 + X) * (1 - Y) =
      1 + X - (Y + Y) - Y * X - X * Y + Y * Y + Y * X * Y := by noncomm_ring
  refine ⟨U, ?_, ?_⟩
  · ext i j
    show p ((U : Matrix (Fin n) (Fin n) C') i j) = (1 : Matrix (Fin n) (Fin n) C) i j
    rw [hU, Matrix.sub_apply, map_sub, hp1, hpY, sub_zero]
  · simp [GG.mat, SemidirectProduct.mul_left, hr]
    rw [hθ, hU, hJ, hg1, key, hYX, hXY, hYY, hY2, zero_mul]
    simp
