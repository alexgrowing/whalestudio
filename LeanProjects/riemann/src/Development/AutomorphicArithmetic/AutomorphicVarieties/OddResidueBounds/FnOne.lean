import Development.AutomorphicArithmetic.AutomorphicVarieties.OddResidueBounds.ZeroMemUnrHom
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.FnCycMap

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum UpperTheory.V.Bern UpperTheory.V.B4 UpperTheory.V.B5 UpperTheory.V.Odd

theorem UpperTheory.V.Odd.fnOne :
    ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (l : ℕ) [Fact l.Prime], Module.finrank E (Fn E Ω l 1) ∣ l - 1 ∧ (∃ ζ : Fn E Ω l 1, IsPrimitiveRoot ζ l) ∧ ∀ N : ℕ, 0 < N → Nonempty (E →ₐ[ℚ] CyclotomicField N ℚ) → Nonempty (Fn E Ω l 1 →ₐ[ℚ] CyclotomicField (l * N) ℚ) := by
  intro E Ω _ _ _ _ _ l hl
  have hl0 : NeZero l := ⟨hl.out.ne_zero⟩
  have hc0 := (UpperTheory.V.Kum.fnCyc E Ω l 1).1
  rw [pow_one] at hc0
  have hc : IsCyclotomicExtension {l} E (Fn E Ω l 1) := hc0
  refine ⟨?_, ⟨_, IsCyclotomicExtension.zeta_spec l E (Fn E Ω l 1)⟩, ?_⟩
  · have hfd : FiniteDimensional E (Fn E Ω l 1) :=
      IsCyclotomicExtension.finiteDimensional {l} E _
    have hg : IsGalois E (Fn E Ω l 1) := IsCyclotomicExtension.isGalois {l} E _
    rw [← IsGalois.card_aut_eq_finrank, ← Nat.totient_prime hl.out, ← ZMod.card_units_eq_totient,
      ← Nat.card_eq_fintype_card]
    exact Subgroup.card_dvd_of_injective _
      (IsPrimitiveRoot.autToPow_injective E (IsCyclotomicExtension.zeta_spec l E (Fn E Ω l 1)))
  · intro N hN ⟨φ⟩
    have hN0 : NeZero N := ⟨hN.ne'⟩
    have hlN0 : NeZero (l * N) := ⟨Nat.mul_ne_zero hl.out.ne_zero hN.ne'⟩
    have hlNq : NeZero ((l * N : ℕ) : ℚ) := ⟨by exact_mod_cast hlN0.out⟩
    have hNq : NeZero ((N : ℕ) : ℚ) := ⟨by exact_mod_cast hN0.out⟩
    letI hcyc : IsCyclotomicExtension {l * N} ℚ (CyclotomicField (l * N) ℚ) :=
      CyclotomicField.isCyclotomicExtension (l * N) ℚ
    letI hcycN : IsCyclotomicExtension {N} ℚ (CyclotomicField N ℚ) :=
      CyclotomicField.isCyclotomicExtension N ℚ
    obtain ⟨ζ, hζ⟩ : ∃ ζ : CyclotomicField (l * N) ℚ, IsPrimitiveRoot ζ (l * N) :=
      ⟨_, IsCyclotomicExtension.zeta_spec (l * N) ℚ (CyclotomicField (l * N) ℚ)⟩
    have hζN : IsPrimitiveRoot (ζ ^ l) N := hζ.pow (Nat.pos_of_ne_zero hlN0.out) rfl
    have hζl : IsPrimitiveRoot (ζ ^ N) l := hζ.pow (Nat.pos_of_ne_zero hlN0.out) (mul_comm l N)
    have hsN : Polynomial.IsSplittingField ℚ (CyclotomicField N ℚ) (Polynomial.X ^ N - 1) :=
      IsCyclotomicExtension.isSplittingField_X_pow_sub_one N ℚ _
    have hsl : Polynomial.IsSplittingField E (Fn E Ω l 1) (Polynomial.X ^ l - 1) :=
      IsCyclotomicExtension.isSplittingField_X_pow_sub_one l E _
    have hsplitN : (Polynomial.map (algebraMap ℚ (CyclotomicField (l * N) ℚ))
        (Polynomial.X ^ N - 1)).Splits := by
      rw [Polynomial.map_sub, Polynomial.map_one, Polynomial.map_pow, Polynomial.map_X]
      have h := Polynomial.X_pow_sub_one_splits hζN
      rwa [Polynomial.C_1] at h
    let ψ := Polynomial.IsSplittingField.lift (CyclotomicField N ℚ)
      (Polynomial.X ^ N - 1 : Polynomial ℚ) hsplitN
    letI : Algebra E (CyclotomicField (l * N) ℚ) := ((ψ.comp φ) : E →+* _).toAlgebra
    have hsplitl : (Polynomial.map (algebraMap E (CyclotomicField (l * N) ℚ))
        (Polynomial.X ^ l - 1)).Splits := by
      rw [Polynomial.map_sub, Polynomial.map_one, Polynomial.map_pow, Polynomial.map_X]
      have h := Polynomial.X_pow_sub_one_splits hζl
      rwa [Polynomial.C_1] at h
    exact ⟨((Polynomial.IsSplittingField.lift (Fn E Ω l 1) (Polynomial.X ^ l - 1 : Polynomial E)
      hsplitl : Fn E Ω l 1 →ₐ[E] _) : Fn E Ω l 1 →+* _).toRatAlgHom⟩
