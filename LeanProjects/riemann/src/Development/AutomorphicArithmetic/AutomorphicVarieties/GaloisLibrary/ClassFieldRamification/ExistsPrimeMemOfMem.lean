import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.ClassFieldRamification.IsClassFieldHilbert
import GroundTheory.GlobalFields.TateThesis.Chebotarev
import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.InertiaRamification.CycInertia
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.ClassFieldRamification.BauerFixIff
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.ClassFieldRamification.RayPrime
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.ClassFieldRamification.SplitCyc

open NumberField IsDedekindDomain IntermediateField UpperTheory.V.Kum UpperTheory.V.CF
open scoped Pointwise

private theorem exists_prime_mem_of_mem {R : Type} [CommRing R] (I : Ideal R) (hI : I.IsPrime) :
    ∀ n : ℕ, n ≠ 0 → (n : R) ∈ I → ∃ p : ℕ, p.Prime ∧ (p : R) ∈ I := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hn hmem
    by_cases h1 : n = 1
    · subst h1
      exact absurd ((Ideal.eq_top_iff_one I).mpr (by simpa using hmem)) hI.ne_top
    · have hp := Nat.minFac_prime h1
      obtain ⟨m, hm⟩ := Nat.minFac_dvd n
      rw [hm, Nat.cast_mul] at hmem
      rcases hI.mem_or_mem hmem with h | h
      · exact ⟨_, hp, h⟩
      · have hm0 : m ≠ 0 := by
          rintro rfl
          rw [mul_zero] at hm
          exact hn hm
        have hlt : m < n := by
          conv_rhs => rw [hm]
          exact lt_mul_of_one_lt_left (Nat.pos_of_ne_zero hm0) hp.one_lt
        exact ih m hlt hm0 h

private theorem cyc_adjoin (K : Type) {L : Type} [Field K] [Field L] [Algebra K L] {n : ℕ} [NeZero n] {ζ : L}
    (hζ : IsPrimitiveRoot ζ n) : IsCyclotomicExtension {n} K K⟮ζ⟯ := by
  change IsCyclotomicExtension {n} K (IntermediateField.adjoin K {ζ}).toSubalgebra
  have hi : IsIntegral K ζ := by
    refine ⟨Polynomial.X ^ n - Polynomial.C 1, Polynomial.monic_X_pow_sub_C 1 (NeZero.ne n), ?_⟩
    simp [hζ.pow_eq_one]
  rw [IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic hi.isAlgebraic]
  exact hζ.adjoin_isCyclotomicExtension K

theorem UpperTheory.V.CF.kwRay :
    ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosed Ω] (𝔪 : GroundTheory.Global.Modulus ℚ) (ζ : Ω), IsPrimitiveRoot ζ (Ideal.absNorm 𝔪.ideal) → 𝔪.rayClassField Ω ≤ ℚ⟮ζ⟯ := by
  intro Ω _ _ _ 𝔪 ζ hζ
  set N := Ideal.absNorm 𝔪.ideal with hN
  have hN0 : N ≠ 0 := by
    rw [hN, Ne, Ideal.absNorm_eq_zero_iff]
    exact 𝔪.ideal_ne_bot
  haveI : NeZero N := ⟨hN0⟩
  have hcyc := cyc_adjoin ℚ hζ
  haveI : NumberField ℚ⟮ζ⟯ := @IsCyclotomicExtension.numberField {N} ℚ ℚ⟮ζ⟯ _ _ _ _ _ hcyc
  have hgal := @IsCyclotomicExtension.isGalois {N} ℚ ℚ⟮ζ⟯ _ _ _ hcyc
  haveI := (GroundTheory.Global.Modulus.isAbelianGalois_rayClassField 𝔪 Ω).toIsGalois
  have hfin : ({v | v.asIdeal ∣ 𝔪.ideal} ∪ {v | v.asIdeal ∣ Ideal.span {(N : 𝓞 ℚ)}} :
      Set (HeightOneSpectrum (𝓞 ℚ))).Finite := by
    refine (Ideal.finite_factors 𝔪.ideal_ne_bot).union (Ideal.finite_factors ?_)
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact_mod_cast hN0
  refine @UpperTheory.V.CF.bauer ℚ Ω _ _ _ _ (𝔪.rayClassField Ω) ℚ⟮ζ⟯ _ _ _
    (by convert hgal; exact Subsingleton.elim _ _) _ hfin ?_
  intro v hv hsplit
  simp only [Set.mem_union, Set.mem_setOf_eq, not_or] at hv
  obtain ⟨_, hv2⟩ := hv
  rw [Ideal.dvd_span_singleton] at hv2
  obtain ⟨p, hp, hpv⟩ := exists_prime_mem_of_mem v.asIdeal v.isPrime
    (Ideal.absNorm v.asIdeal) (by rw [Ne, Ideal.absNorm_eq_zero_iff]; exact v.ne_bot)
    (Ideal.absNorm_mem _)
  have hpN : ¬ p ∣ N := by
    rintro ⟨k, hk⟩
    apply hv2
    rw [hk, Nat.cast_mul]
    exact v.asIdeal.mul_mem_right _ hpv
  have hmod : p ≡ 1 [MOD N] := by
    haveI hc2 : IsCyclotomicExtension {N} ℚ ℚ⟮ζ⟯ := by
      convert hcyc
      all_goals first
        | rfl
        | exact Subsingleton.elim _ _
    refine UpperTheory.V.CF.splitCyc N ℚ⟮ζ⟯ v p hp hpv hpN ?_
    convert hsplit
    all_goals first
      | rfl
      | exact Subsingleton.elim _ _
  obtain ⟨hv', hcls⟩ := UpperTheory.V.CF.rayPrime 𝔪 v p hp hpv hmod
  exact (GroundTheory.Global.Modulus.splitsCompletely_rayClassField_iff 𝔪 Ω hv').mpr hcls
