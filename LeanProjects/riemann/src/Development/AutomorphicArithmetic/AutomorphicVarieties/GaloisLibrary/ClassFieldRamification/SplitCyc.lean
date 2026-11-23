import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.ClassFieldRamification.IsClassFieldHilbert
import GroundTheory.GlobalFields.TateThesis.Chebotarev
import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.InertiaRamification.CycInertia

open NumberField IsDedekindDomain IntermediateField UpperTheory.V.Kum UpperTheory.V.CF
open scoped Pointwise

theorem UpperTheory.V.CF.splitCyc :
    ∀ (N : ℕ) [NeZero N] (C : Type) [Field C] [NumberField C] [IsCyclotomicExtension {N} ℚ C] (v : HeightOneSpectrum (𝓞 ℚ)) (p : ℕ), p.Prime → (p : 𝓞 ℚ) ∈ v.asIdeal → ¬ p ∣ N → GroundTheory.Global.SplitsCompletely C v → p ≡ 1 [MOD N] := by
  intro N _ C _ _ _ v p hp hpv hpN hspl
  haveI := Fact.mk hp
  haveI := v.isMaximal
  have hspan : (Ideal.span {(p : ℤ)}).IsMaximal :=
    PrincipalIdealRing.isMaximal_of_irreducible (Nat.prime_iff_prime_int.mp hp).irreducible
  have hvZ : v.asIdeal.under ℤ = Ideal.span {(p : ℤ)} := by
    refine (hspan.eq_of_le (Ideal.IsPrime.under ℤ v.asIdeal).ne_top ?_).symm
    rw [Ideal.span_singleton_le_iff_mem, Ideal.under, Ideal.mem_comap, map_natCast]
    exact hpv
  haveI : v.asIdeal.LiesOver (Ideal.span {(p : ℤ)}) := ⟨hvZ.symm⟩
  have hsurj : Function.Surjective (algebraMap ℤ (𝓞 ℚ)) := fun y => ⟨Rat.ringOfIntegersEquiv y, by
    have h : (Rat.ringOfIntegersEquiv.symm : ℤ →+* 𝓞 ℚ) = algebraMap ℤ (𝓞 ℚ) :=
      Subsingleton.elim _ _
    rw [← h]
    exact Rat.ringOfIntegersEquiv.symm_apply_apply y⟩
  have hv1 : v.asIdeal.inertiaDeg ℤ = 1 := by
    letI := Ideal.Quotient.field (Ideal.span {(p : ℤ)})
    letI := Ideal.Quotient.field v.asIdeal
    rw [Ideal.inertiaDeg_eq_of_isMaximal (Ideal.span {(p : ℤ)}) v.asIdeal,
      finrank_eq_one_iff_of_nonzero (1 : 𝓞 ℚ ⧸ v.asIdeal) one_ne_zero, eq_top_iff]
    rintro y -
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
    obtain ⟨a, rfl⟩ := hsurj y
    rw [Submodule.mem_span_singleton]
    refine ⟨Ideal.Quotient.mk _ a, ?_⟩
    rw [Algebra.smul_def, mul_one]
    rfl
  obtain ⟨⟨P, hPp, hPl⟩⟩ := v.asIdeal.nonempty_primesOver (S := 𝓞 C)
  have hPne : P ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot v.ne_bot P
  have hs := hspl ⟨P, hPp, hPne⟩ hPl
  haveI : P.LiesOver (Ideal.span {(p : ℤ)}) := Ideal.LiesOver.trans P v.asIdeal _
  have ht := Ideal.inertiaDeg_tower (R := ℤ) v.asIdeal P
  rw [hv1, one_mul, hs.2, IsCyclotomicExtension.Rat.inertiaDeg_eq_of_not_dvd p C P hpN] at ht
  rw [← ZMod.natCast_eq_natCast_iff, Nat.cast_one]
  exact orderOf_eq_one_iff.mp ht
