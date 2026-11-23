import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.BaseRepGL3NormalisedOfPsiEqOne

open Matrix UpperTheory.V.U3

private theorem sgnAct_tor {R : Type} [CommRing R] (s : ℤˣ) (t : Rˣ) :
    sgnAct 3 R s (tor R t) = tor R t := by
  by_cases hs : s = 1
  · subst hs
    exact sgnAct_one _
  · simp only [sgnAct, MonoidHom.coe_mk, OneHom.coe_mk, if_neg hs]
    exact theta_tor t

private theorem conj_left {G R : Type} [Group G] [CommRing R] (r : G →* GG 3 R) (t : Rˣ) (g : G) :
    (conjBy (tor R t) r g).left = tor R t * (r g).left * tor R t⁻¹ := by
  simp [conjBy, MulAut.conj_apply, SemidirectProduct.mul_left, SemidirectProduct.inv_left, sgnAct_tor, map_inv]

private theorem conj_right {G R : Type} [Group G] [CommRing R] (r : G →* GG 3 R) (t : Rˣ) (g : G) :
    (conjBy (tor R t) r g).right = (r g).right := by
  simp [conjBy, MulAut.conj_apply, SemidirectProduct.mul_right, SemidirectProduct.inv_right]

private theorem conj_mat {G R : Type} [Group G] [CommRing R] (r : G →* GG 3 R) (t : Rˣ) (g : G)
    (a b : Fin 3) :
    (conjBy (tor R t) r g).mat a b = ((t ^ wt a b : Rˣ) : R) * (r g).mat a b := by
  show (((conjBy (tor R t) r g).left : GL (Fin 3) R) : Matrix (Fin 3) (Fin 3) R) a b = _
  rw [conj_left, Units.val_mul, Units.val_mul, tor_val, tor_val, mul_diagonal, diagonal_mul]
  have key : ((t ^ wt1 a : Rˣ) : R) * ((t⁻¹ ^ wt1 b : Rˣ) : R) = ((t ^ wt a b : Rˣ) : R) := by
    rw [← Units.val_mul, wt, _root_.zpow_sub, _root_.inv_zpow]
  rw [← key, GG.mat]
  ring

private theorem conj_zmat {G R : Type} [Group G] [CommRing R] (r : G →* GG 3 R) (t : Rˣ) (c g₁ : G)
    (a b : Fin 3) :
    zmat c g₁ (conjBy (tor R t) r) a b = ((t ^ wt a b : Rˣ) : R) * zmat c g₁ r a b := by
  simp only [zmat, Matrix.sub_apply, conj_mat, mul_sub]

theorem UpperTheory.V.U3.conjBy_tor :
    ∀ {G R : Type} [Group G] [CommRing R] (r : G →* GG 3 R) (t : Rˣ),
    (∀ g a b, (conjBy (tor R t) r g).mat a b = ((t ^ wt a b : Rˣ) : R) * (r g).mat a b) ∧ (∀ g, (conjBy (tor R t) r g).right = (r g).right) ∧
    (∀ c g₁, Normalised c g₁ r → Normalised c g₁ (conjBy (tor R t) r)) ∧ (∀ c g₁, zeta c g₁ (conjBy (tor R t) r) = zeta c g₁ r) ∧
    ∀ (η : G →* ℤˣ) (Ψ : G →* Rˣ), conjBy (tor R t) (r0 η Ψ) = r0 η Ψ := by
  intro G R _ _ r t
  refine ⟨conj_mat r t, conj_right r t, ?_, ?_, ?_⟩
  · intro c g₁ h
    refine ⟨?_, ?_, ?_⟩
    · ext a b
      rw [conj_mat, h.atc]
      by_cases hab : a = b
      · subst hab
        simp [wt]
      · simp [Matrix.one_apply_ne hab]
    · rw [conj_zmat, h.z12, mul_zero]
    · rw [conj_zmat, h.z21, mul_zero]
  · intro c g₁
    unfold zeta
    rw [conj_zmat]
    simp [wt]
  · intro η Ψ
    refine MonoidHom.ext fun g => ?_
    refine SemidirectProduct.ext ?_ (conj_right _ t g)
    rw [conj_left, unitaryThreeReflection_left, ← map_mul, ← map_mul, mul_inv_cancel_comm]
