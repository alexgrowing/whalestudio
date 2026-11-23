import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.BaseRepGL3NormalisedOfPsiEqOne

open Matrix UpperTheory.V.U3

private theorem gstar_right_and_mat_of_right_neg_one_mat_one {G R : Type} [Group G] [CommRing R] (r : G →* GG 3 R) (c g₁ : G)
    (hc : (r c).right = -1) (h1 : (r g₁).right = 1) (hN : (r c).mat = 1) :
    (r (gstar c g₁)).right = 1 ∧ (r (gstar c g₁)).mat = Jmat R 3 * ((r g₁).mat)ᵀ * Jmat R 3 := by
  have hcl : (r c).left = 1 := Units.ext hN
  refine ⟨by simp [gstar, hc, h1], ?_⟩
  have hL : (r (gstar c g₁)).left = theta ((r g₁).left⁻¹) := by
    simp only [gstar, map_mul, map_inv, SemidirectProduct.mul_left, SemidirectProduct.inv_left,
      SemidirectProduct.mul_right, SemidirectProduct.inv_right, hcl, hc, h1]
    simp [sgnAct, thetaAut]
    have e1 : theta (1 : GL (Fin 3) R) = 1 := map_one (thetaAut 3 R)
    have e2 : theta ((r g₁).left⁻¹) = (theta (r g₁).left)⁻¹ := map_inv (thetaAut 3 R) _
    rw [e1, mul_one, e2]
  show ((r (gstar c g₁)).left : Matrix (Fin 3) (Fin 3) R) = _
  rw [hL, theta_val, inv_inv]
  rfl

private theorem cob_mul_mat_eq_commutator_of_right_eq_one {G R : Type} [Group G] [CommRing R] (r : G →* GG 3 R)
    (X : Matrix (Fin 3) (Fin 3) R) (g : G) (hg : (r g).right = 1) :
    cob r X g * (r g).mat = X * (r g).mat - (r g).mat * X := by
  show (X - (r g).adFun X) * (r g).mat = _
  simp only [GG.adFun, hg, if_true]
  show (X - (r g).mat * X * ((r g).left⁻¹ : GL (Fin 3) R)) * ((r g).left : Matrix (Fin 3) (Fin 3) R) = _
  rw [sub_mul, mul_assoc, Units.inv_mul, mul_one]
  rfl

theorem UpperTheory.V.U3.normCoc_cob_iff :
    ∀ {G R : Type} [Group G] [CommRing R] (r : G →* GG 3 R) (c g₁ : G) (X : Matrix (Fin 3) (Fin 3) R), IsUnit (2 : R) → (r c).right = -1 → (r g₁).right = 1 →
      Normalised c g₁ r → IsUnit (zeta c g₁ r) → (NormCoc c g₁ r (cob r X) ↔ X ∈ unitaryThreeTorusLieAlgebra R) := by
  intro G R _ _ r c g₁ X h2 hc h1 hn hz
  obtain ⟨hsr, hsm⟩ := gstar_right_and_mat_of_right_neg_one_mat_one r c g₁ hc h1 hn.atc
  have hcl : (r c).left = 1 := Units.ext hn.atc
  have hA : cob r X c = X - thetaLie X := by
    show X - (r c).adFun X = _
    have hne : (r c).right ≠ 1 := by rw [hc]; decide
    simp only [GG.adFun, if_neg hne, hn.atc, one_mul]
    rw [hcl, inv_one, Units.val_one, mul_one]
  have hW : zvar c g₁ r (cob r X) = X * ((r g₁).mat - Jmat R 3 * ((r g₁).mat)ᵀ * Jmat R 3)
      - ((r g₁).mat - Jmat R 3 * ((r g₁).mat)ᵀ * Jmat R 3) * X := by
    show cob r X g₁ * (r g₁).mat - cob r X (gstar c g₁) * (r (gstar c g₁)).mat = _
    rw [cob_mul_mat_eq_commutator_of_right_eq_one r X g₁ h1, cob_mul_mat_eq_commutator_of_right_eq_one r X _ hsr, hsm]
    noncomm_ring
  set M := (r g₁).mat with hM
  have z12 : M 0 1 - M 1 2 = 0 := by
    have h := hn.z12
    simp only [zmat, hsm] at h
    simp [Jmat, Matrix.mul_apply, Fin.sum_univ_three, Fin.rev] at h
    linear_combination h
  have z21 : M 1 0 - M 2 1 = 0 := by
    have h := hn.z21
    simp only [zmat, hsm] at h
    simp [Jmat, Matrix.mul_apply, Fin.sum_univ_three, Fin.rev] at h
    linear_combination h
  have hu : IsUnit (M 0 0 - M 2 2) := by
    have e : zeta c g₁ r = M 0 0 - M 2 2 := by
      simp only [zeta, zmat, hsm]
      simp [Jmat, Matrix.mul_apply, Fin.sum_univ_three, Fin.rev]
      rfl
    rw [← e]; exact hz
  constructor
  · rintro ⟨ha, h12, h21⟩
    rw [hA] at ha
    rw [hW] at h12 h21
    have a00 := congrFun (congrFun ha 0) 0
    have a11 := congrFun (congrFun ha 1) 1
    have a02 := congrFun (congrFun ha 0) 2
    have a20 := congrFun (congrFun ha 2) 0
    have a01 := congrFun (congrFun ha 0) 1
    have a10 := congrFun (congrFun ha 1) 0
    simp [thetaLie, Jmat, Matrix.mul_apply, Fin.sum_univ_three, Fin.rev] at a00 a11 a02 a20 a01 a10
    simp [Jmat, Matrix.mul_apply, Fin.sum_univ_three, Fin.rev] at h12 h21
    have x11 : X 1 1 = 0 := h2.mul_left_cancel (by linear_combination a11)
    have x02 : X 0 2 = 0 := h2.mul_left_cancel (by linear_combination a02)
    have x20 : X 2 0 = 0 := h2.mul_left_cancel (by linear_combination a20)
    have x01 : X 0 1 = 0 := hu.mul_left_cancel
      (by linear_combination -h12 + X 0 0 * z12 - X 0 2 * z21 - X 1 1 * z12)
    have x10 : X 1 0 = 0 := hu.mul_left_cancel
      (by linear_combination h21 - X 1 1 * z21 + X 0 0 * z21 - X 2 0 * z12)
    have x12 : X 1 2 = 0 := by linear_combination a01 - x01
    have x21 : X 2 1 = 0 := by linear_combination a10 - x10
    have x22 : X 2 2 = -X 0 0 := by linear_combination a00
    rw [unitaryThreeTorusLieAlgebra, Submodule.mem_span_singleton]
    refine ⟨X 0 0, ?_⟩
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [wt1, Matrix.diagonal, x01, x10, x02, x20, x11, x12, x21, x22] <;> ring
  · intro hX
    rw [unitaryThreeTorusLieAlgebra, Submodule.mem_span_singleton] at hX
    obtain ⟨a, rfl⟩ := hX
    refine ⟨?_, ?_, ?_⟩
    · rw [hA]
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [thetaLie, Jmat, wt1, Matrix.mul_apply, Fin.sum_univ_three, Fin.rev, Matrix.diagonal] <;> ring
    · rw [hW]
      simp [Jmat, wt1, Matrix.mul_apply, Fin.sum_univ_three, Fin.rev, Matrix.diagonal]
      linear_combination a * z12
    · rw [hW]
      simp [Jmat, wt1, Matrix.mul_apply, Fin.sum_univ_three, Fin.rev, Matrix.diagonal]
      linear_combination a * z21
