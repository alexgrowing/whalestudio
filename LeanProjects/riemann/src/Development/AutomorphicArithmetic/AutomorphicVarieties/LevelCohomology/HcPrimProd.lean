import Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.HcDefs
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.EtaKer

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V UpperTheory.V.Base UpperTheory.V.HV UpperTheory.V.X

theorem UpperTheory.V.X.primProd :
    ∀ (O : Type) [CommRing O] [IsDomain O] (M N : ℕ) [NeZero M] [NeZero N] (χ : DirichletCharacter O M) (θ : DirichletCharacter O N), ∃ (f : ℕ) (φ : DirichletCharacter O f), φ.IsPrimitive ∧ f ∣ M * θ.conductor ∧ (∀ t : ℕ, χ ^ t = 1 → θ ^ t = 1 → φ ^ t = 1) ∧ ∀ a : ℤ, IsCoprime a (M * N : ℕ) → φ a = χ a * θ a := by
  intro O _ _ M N _ _ χ θ
  have hc0 : θ.conductor ≠ 0 := θ.conductor_ne_zero
  haveI : NeZero θ.conductor := ⟨hc0⟩
  haveI : NeZero (M * θ.conductor) := ⟨mul_ne_zero (NeZero.ne M) hc0⟩
  set θ' := θ.primitiveCharacter with hθe
  have hM : M ∣ M * θ.conductor := dvd_mul_right M _
  have hC : θ.conductor ∣ M * θ.conductor := dvd_mul_left _ M
  set ψ : DirichletCharacter O (M * θ.conductor) :=
    DirichletCharacter.changeLevel hM χ * DirichletCharacter.changeLevel hC θ' with hψe
  refine ⟨ψ.conductor, ψ.primitiveCharacter, ψ.primitiveCharacter_isPrimitive, ψ.conductor_dvd_level, ?_, ?_⟩
  · intro t hχ hθ
    have hθ1 : θ' ^ t = 1 := by
      rw [← DirichletCharacter.changeLevel_eq_one_iff θ.conductor_dvd_level, map_pow,
        DirichletCharacter.changeLevel_primitiveCharacter]
      exact hθ
    have hψ1 : ψ ^ t = 1 := by
      rw [hψe, mul_pow, ← map_pow, ← map_pow, hχ, hθ1, map_one, map_one, mul_one]
    rw [← DirichletCharacter.changeLevel_eq_one_iff ψ.conductor_dvd_level, map_pow,
      DirichletCharacter.changeLevel_primitiveCharacter]
    exact hψ1
  · intro a ha
    rw [Nat.cast_mul] at ha
    have haM : IsCoprime a (M : ℤ) := ha.of_mul_right_left
    have haN : IsCoprime a (N : ℤ) := ha.of_mul_right_right
    have haC : IsCoprime a (θ.conductor : ℤ) :=
      haN.of_isCoprime_of_dvd_right (Int.natCast_dvd_natCast.mpr θ.conductor_dvd_level)
    have haMC : IsCoprime a ((M * θ.conductor : ℕ) : ℤ) := by
      rw [Nat.cast_mul]
      exact haM.mul_right haC
    rw [ψ.primitiveCharacter_apply_of_isCoprime haMC, hψe, MulChar.mul_apply,
      DirichletCharacter.changeLevel_eq_cast_of_dvd' χ hM haMC,
      DirichletCharacter.changeLevel_eq_cast_of_dvd' θ' hC haMC,
      θ.primitiveCharacter_apply_of_isCoprime haN]
