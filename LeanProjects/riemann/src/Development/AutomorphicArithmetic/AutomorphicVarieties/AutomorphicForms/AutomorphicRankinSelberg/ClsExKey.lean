import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.AutomorphicRankinSelberg.StripInt

open CongruenceSubgroup UpperHalfPlane
open scoped MatrixGroups

private theorem clsEx_key (L : ℕ) (ψ : DirichletCharacter ℂ L) (F : ℍ → ℂ)
    (hF : ∀ γ : SL(2, ℤ), γ ∈ Gamma0 L → ∀ z, F (γ • z) = ψ ((γ 1 1 : ℤ) : ZMod L) * F z)
    (n m : ℕ) (γ δ : SL(2, ℤ))
    (h : UpperTheory.V.Af.Rs.cls L ((m : ℤ) • UpperTheory.V.Af.Rs.row δ) = UpperTheory.V.Af.Rs.cls L ((n : ℤ) • UpperTheory.V.Af.Rs.row γ))
    (z : ℍ) : ψ (m : ZMod L) * F (δ • z) = ψ (n : ZMod L) * F (γ • z) := by
  classical
  have h0 := congrFun h 0
  have h1 := congrFun h 1
  simp only [UpperTheory.V.Af.Rs.cls, UpperTheory.V.Af.Rs.row, Pi.smul_apply, smul_eq_mul, Int.cast_mul,
    Int.cast_natCast] at h0 h1
  have hdet : ((γ 0 0 : ℤ) : ZMod L) * (γ 1 1 : ℤ) - (γ 0 1 : ℤ) * (γ 1 0 : ℤ) = 1 := by
    have := γ.det_coe
    rw [Matrix.det_fin_two] at this
    exact_mod_cast congrArg (fun t : ℤ => (t : ZMod L)) this
  have hn : (n : ZMod L) = m * (((γ 0 0 : ℤ) : ZMod L) * (δ 1 1 : ℤ) - (γ 0 1 : ℤ) * (δ 1 0 : ℤ)) := by
    linear_combination (-(n : ZMod L)) * hdet - ((γ 0 0 : ℤ) : ZMod L) * h1 +
      ((γ 0 1 : ℤ) : ZMod L) * h0
  by_cases hm : IsUnit (m : ZMod L)
  · obtain ⟨η, hη⟩ : ∃ η : SL(2, ℤ), η = δ * γ⁻¹ := ⟨_, rfl⟩
    have e10 : (η 1 0 : ℤ) = δ 1 0 * γ 1 1 - δ 1 1 * γ 1 0 := by
      rw [hη]
      simp [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_inv,
        Matrix.adjugate_fin_two, Matrix.mul_apply, Fin.sum_univ_two]
      ring
    have e11 : (η 1 1 : ℤ) = δ 1 1 * γ 0 0 - δ 1 0 * γ 0 1 := by
      rw [hη]
      simp [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_inv,
        Matrix.adjugate_fin_two, Matrix.mul_apply, Fin.sum_univ_two]
      ring
    have hmem : η ∈ Gamma0 L := by
      rw [Gamma0_mem, e10]
      push_cast
      refine (hm.mul_right_eq_zero).1 ?_
      linear_combination ((γ 1 1 : ℤ) : ZMod L) * h0 - ((γ 1 0 : ℤ) : ZMod L) * h1
    have hδ : δ = η * γ := by
      rw [hη, inv_mul_cancel_right]
    have hn' : (n : ZMod L) = m * ((η 1 1 : ℤ) : ZMod L) := by
      rw [e11, hn]
      push_cast
      ring
    rw [hδ, mul_smul, hF η hmem, hn', map_mul]
    ring
  · have hn' : ¬IsUnit (n : ZMod L) := by
      intro hu
      rw [hn] at hu
      exact hm (isUnit_of_mul_isUnit_left hu)
    rw [MulChar.map_nonunit _ hm, MulChar.map_nonunit _ hn']
    simp

theorem UpperTheory.V.Af.Rs.clsEx :
    UpperTheory.V.Af.Rs.RowBij → UpperTheory.V.Af.Rs.ClsEx := by
  intro _ L _ ψ F hF
  classical
  refine ⟨fun v z => if h : ∃ p : ℕ × SL(2, ℤ), cls L ((p.1 : ℤ) • row p.2) = v then
    ψ (h.choose.1 : ZMod L) * F (h.choose.2 • z) else 0, ?_⟩
  intro n γ z
  have h : ∃ p : ℕ × SL(2, ℤ), cls L ((p.1 : ℤ) • row p.2) = cls L ((n : ℤ) • row γ) := ⟨(n, γ), rfl⟩
  simp only [dif_pos h]
  exact clsEx_key L ψ F hF n _ γ _ h.choose_spec z
