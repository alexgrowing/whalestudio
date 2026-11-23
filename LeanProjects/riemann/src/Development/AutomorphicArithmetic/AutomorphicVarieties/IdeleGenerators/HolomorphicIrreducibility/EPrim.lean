import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.ConstSmall

theorem UpperTheory.V.Sd.ePrim :
    UpperTheory.V.Sd.EPrim := by
  intro l M w φ θ χ D
  have hM := D.one_lt
  have hw := D.prime
  haveI : NeZero M := ⟨by omega⟩
  haveI : NeZero w := ⟨hw.ne_zero⟩
  haveI : NeZero (M * w) := ⟨mul_ne_zero (NeZero.ne M) (NeZero.ne w)⟩
  set A := DirichletCharacter.changeLevel (dvd_mul_right M w) φ with hA
  set B := DirichletCharacter.changeLevel (dvd_mul_left w M) θ with hB
  have hχ : χ = A * B := by
    ext u
    have h1 := D.mul (u : ZMod (M * w)).val
    rw [MulChar.mul_apply, hA, hB, DirichletCharacter.changeLevel_eq_cast_of_dvd,
      DirichletCharacter.changeLevel_eq_cast_of_dvd, ← ZMod.natCast_val, ← ZMod.natCast_val,
      ← h1, ZMod.natCast_zmod_val]
  have hAc : A.conductor = M := by
    rw [hA, DirichletCharacter.conductor_changeLevel]
    exact D.prim
  have hBc : B.conductor = w := by
    rw [hB, DirichletCharacter.conductor_changeLevel]
    rcases (Nat.dvd_prime hw).mp θ.conductor_dvd_level with h | h
    · exact absurd (DirichletCharacter.eq_one_iff_conductor_eq_one.mpr h) D.θne
    · exact h
  have hcop : M.Coprime w := ((Nat.Prime.coprime_iff_not_dvd hw).mpr D.wM).symm
  have h1 : M ∣ χ.conductor := by
    have h := DirichletCharacter.conductor_mul_dvd_lcm_conductor χ B⁻¹
    rw [DirichletCharacter.conductor_inv, hBc] at h
    have e : χ * B⁻¹ = A := by rw [hχ, mul_inv_cancel_right]
    rw [e, hAc] at h
    exact hcop.dvd_of_dvd_mul_right (h.trans (Nat.lcm_dvd_mul _ _))
  have h2 : w ∣ χ.conductor := by
    have h := DirichletCharacter.conductor_mul_dvd_lcm_conductor A⁻¹ χ
    rw [DirichletCharacter.conductor_inv, hAc] at h
    have e : A⁻¹ * χ = B := by rw [hχ, inv_mul_cancel_left]
    rw [e, hBc] at h
    exact hcop.symm.dvd_of_dvd_mul_left (h.trans (Nat.lcm_dvd_mul _ _))
  exact Nat.dvd_antisymm χ.conductor_dvd_level (hcop.mul_dvd_of_dvd_of_dvd h1 h2)
