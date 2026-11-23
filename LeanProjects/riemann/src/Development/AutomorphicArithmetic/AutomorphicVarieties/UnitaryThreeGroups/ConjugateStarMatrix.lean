import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.BaseRepGL3NormalisedOfPsiEqOne

open Matrix UpperTheory.V.U3

private theorem conjugate_star_matrix {G R : Type} [Group G] [CommRing R] (r : G →* GG 3 R) (c g : G)
    (hc : (r c).right = -1) (hg : (r g).right = 1) (hm : (r c).mat = 1) :
    (r (gstar c g)).mat = Jmat R 3 * (r g).matᵀ * Jmat R 3 := by
  have hc' : r c = SemidirectProduct.mk 1 (-1) := by
    apply SemidirectProduct.ext
    · exact Units.ext (by simpa [GG.mat] using hm)
    · exact hc
  have hg' : r g = SemidirectProduct.mk (r g).left 1 := SemidirectProduct.ext rfl hg
  have hs : r (gstar c g) = r c * (r g)⁻¹ * r c := by
    simp only [gstar, map_mul, map_inv]
  rw [hs, hc', hg']
  simp only [GG.mat, SemidirectProduct.mul_left, SemidirectProduct.mul_right, SemidirectProduct.inv_left,
    SemidirectProduct.inv_right, inv_one, map_one, mul_one, one_mul, MulAut.one_apply, map_inv,
    sgnAct_neg_one, theta_inv_val]

theorem UpperTheory.V.U3.zmat_diag :
    ∀ {G R : Type} [Group G] [CommRing R] (r : G →* GG 3 R) (c g₁ : G), IsUnit (2 : R) → (r c).right = -1 → (r g₁).right = 1 → Normalised c g₁ r →
    zmat c g₁ r = Matrix.diagonal ![zeta c g₁ r, 0, -zeta c g₁ r] := by
  intro G R _ _ r c g₁ _ hc hg hN
  have hJ : ∀ (M : Matrix (Fin 3) (Fin 3) R) (i j : Fin 3), (Jmat R 3 * Mᵀ * Jmat R 3) i j = M j.rev i.rev := by
    intro M i j
    simp only [Matrix.mul_apply, Jmat, Matrix.transpose_apply, ite_mul, mul_ite, one_mul, zero_mul, mul_zero,
      Finset.sum_ite_eq', Finset.sum_ite_eq, Finset.mem_univ, if_true]
    rw [Finset.sum_eq_single j.rev]
    · simp
    · intro x _ hx
      rw [if_neg]
      intro h
      exact hx (by rw [h, Fin.rev_rev])
    · simp
  have hZ : ∀ i j : Fin 3, zmat c g₁ r i j = (r g₁).mat i j - (r g₁).mat j.rev i.rev := by
    intro i j
    simp only [zmat, Matrix.sub_apply]
    rw [conjugate_star_matrix r c g₁ hc hg hN.atc, hJ]
  have h01 := hN.z12
  have h10 := hN.z21
  rw [hZ] at h01 h10
  have e0 : (0 : Fin 3).rev = 2 := rfl
  have e1 : (1 : Fin 3).rev = 1 := rfl
  have e2 : (2 : Fin 3).rev = 0 := rfl
  rw [e0, e1] at h01 h10
  ext i j
  simp only [zeta]
  rw [hZ, hZ 0 0, e0]
  fin_cases i <;> fin_cases j <;> simp [e0, e1, e2, Matrix.diagonal] <;>
    first
    | linear_combination h01
    | linear_combination -h01
    | linear_combination h10
    | linear_combination -h10
