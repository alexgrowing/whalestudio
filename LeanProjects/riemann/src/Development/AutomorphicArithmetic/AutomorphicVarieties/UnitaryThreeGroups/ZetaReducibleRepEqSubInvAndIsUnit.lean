import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.BaseRepGL3NormalisedOfPsiEqOne

open Matrix UpperTheory.V.U3

theorem UpperTheory.V.U3.zeta_reducible_rep_eq_sub_inv_and_isUnit :
    ∀ {G R : Type} [Group G] [CommRing R] (η : G →* ℤˣ) (Ψ : G →* Rˣ) (c g₁ : G), Marks η Ψ c g₁ →
    zeta c g₁ (r0 η Ψ) = ((Ψ g₁ : Rˣ) : R) - (((Ψ g₁)⁻¹ : Rˣ) : R) ∧ IsUnit (zeta c g₁ (r0 η Ψ)) := by
  intro G R _ _ η Ψ c g₁ hm
  have hz : zeta c g₁ (r0 η Ψ) = ((Ψ g₁ : Rˣ) : R) - (((Ψ g₁)⁻¹ : Rˣ) : R) := by
    have hs : Ψ (gstar c g₁) = (Ψ g₁)⁻¹ := by
      simp [gstar, map_mul, map_inv, hm.Ψc]
    simp only [zeta, zmat, GG.mat, unitaryThreeReflection_left, tor_val, Matrix.sub_apply, Matrix.diagonal_apply_eq, hs]
    simp [wt1]
  refine ⟨hz, ?_⟩
  rw [hz]
  have key : ((Ψ g₁ : Rˣ) : R) - (((Ψ g₁)⁻¹ : Rˣ) : R)
      = (((Ψ g₁)⁻¹ : Rˣ) : R) * (((Ψ g₁ : Rˣ) : R) ^ 2 - 1) := by
    rw [mul_sub, mul_one, pow_two, ← mul_assoc, Units.inv_mul, one_mul]
  rw [key]
  exact (Units.isUnit _).mul hm.Ψg
