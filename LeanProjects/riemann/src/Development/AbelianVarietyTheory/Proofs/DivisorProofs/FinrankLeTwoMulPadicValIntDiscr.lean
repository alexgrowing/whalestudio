import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.MemPass
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
import Development.AbelianVarietyTheory.Definitions.Divisors.HasLevelStd
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModDefs
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.VpBounds
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.PadicValNatAbsNormEqZero

open NumberField IsDedekindDomain UniqueFactorizationMonoid

namespace GlobalTheory.RootDiscrExp

open ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf

theorem finrank_le_two_mul_padicValInt_discr (E : Type) [Field E] [NumberField E] [IsGalois ℚ E] (p : ℕ)
    (hp : p.Prime) (hd : (p : ℤ) ∣ discr E) : Module.finrank ℚ E ≤ 2 * padicValInt p (discr E) := by
  classical
  have := Fact.mk hp
  have hd0 : (discr E).natAbs ≠ 0 := Int.natAbs_ne_zero.2 (discr_ne_zero E)
  obtain ⟨a, m, hm, hdisc⟩ := Nat.exists_eq_pow_mul_and_not_dvd hd0 p hp.ne_one
  have hm0 : m ≠ 0 := by
    rintro rfl
    exact hm (dvd_zero p)
  have ha : padicValInt p (discr E) = a := by
    rw [padicValInt, hdisc, padicValNat.mul (pow_ne_zero _ hp.ne_zero) hm0, padicValNat.prime_pow,
      padicValNat.eq_zero_of_not_dvd hm, add_zero]
  have ha0 : a ≠ 0 := by
    rintro rfl
    apply hm
    have h1 := Int.natCast_dvd.1 hd
    rwa [hdisc, pow_zero, one_mul] at h1
  have hpmax : (Ideal.span {(p : ℤ)}).IsMaximal :=
    PrincipalIdealRing.isMaximal_of_irreducible (Nat.prime_iff_prime_int.mp hp).irreducible
  have hp0 : Ideal.span {(p : ℤ)} ≠ ⊥ := by
    rw [Ne, Ideal.span_singleton_eq_bot]
    exact Nat.cast_ne_zero.2 hp.ne_zero
  obtain ⟨P, hPmax, hPo⟩ := Ideal.exists_maximal_ideal_liesOver_of_isIntegral (S := 𝓞 E) (Ideal.span {(p : ℤ)})
  have hP : P.IsPrime := hPmax.isPrime
  have hpP : (p : 𝓞 E) ∈ P := by
    have h1 : (p : ℤ) ∈ P.under ℤ := by
      rw [← hPo.over]
      exact Ideal.mem_span_singleton_self _
    rwa [Ideal.under_def, Ideal.mem_comap, map_natCast] at h1
  have h := diffExp E p a m hp hm hdisc P hP hpP
  have hpos := count_span_pos E p hp hP hpP
  have hD0 : differentIdeal ℤ (𝓞 E) ≠ ⊥ := differentIdeal_ne_bot
  have hI0 : Ideal.span {(p : 𝓞 E)} ≠ ⊥ := span_nat_ne_bot p
  have hdvd : P ^ (multiplicity P (Ideal.span {(p : 𝓞 E)}) - 1) ∣ differentIdeal ℤ (𝓞 E) := by
    refine pow_sub_one_dvd_differentIdeal ℤ (p := Ideal.span {(p : ℤ)}) P _ hp0 ?_
    rw [Ideal.map_span, Set.image_singleton, map_natCast]
    exact pow_multiplicity_dvd _ _
  have hP0 : P ≠ ⊥ := by
    rintro rfl
    exact natCast_ne_zero_oe (E := E) p ((Submodule.mem_bot _).1 hpP)
  have fD := FiniteMultiplicity.of_prime_left (Ideal.prime_of_isPrime hP0 hP) hD0
  have hd' := fD.le_multiplicity_of_pow_dvd hdvd
  have hc : ∀ X : Ideal (𝓞 E), X ≠ ⊥ → (normalizedFactors X).count P = multiplicity P X := fun X hX =>
    (⟨P, hP, hP0⟩ : HeightOneSpectrum (𝓞 E)).count_normalizedFactors_eq_multiplicity hX
  rw [hc _ hD0, hc _ hI0] at h
  rw [hc _ hI0] at hpos
  rw [ha]
  generalize multiplicity P (differentIdeal ℤ (𝓞 E)) = k at h hd'
  generalize multiplicity P (Ideal.span {(p : 𝓞 E)}) = e at h hd' hpos
  generalize Module.finrank ℚ E = n at h ⊢
  have hk : k ≠ 0 := by
    rintro rfl
    have : a * e ≠ 0 := mul_ne_zero ha0 hpos.ne'
    apply this
    nlinarith
  have hek : e ≤ 2 * k := by omega
  refine Nat.le_of_mul_le_mul_right ?_ hpos
  nlinarith [Nat.mul_le_mul_left n hek]

theorem half_le_delta_two_vp : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [IsAbelianGalois ℚ E] (I : Type)
    [Fintype I] (d : ℕ) (φ : I → E →+* ℂ), GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds.IsFieldData d φ →
    (1 / 2 : ℝ) ≤ GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds.delta_vp E 2 := by
  intro E _ _ _ _ I _ d φ h
  have h1 := finrank_le_two_mul_padicValInt_discr E 2 Nat.prime_two (by exact_mod_cast h.2.2.2.2.1)
  have hn : (0 : ℝ) < Module.finrank ℚ E := by exact_mod_cast Module.finrank_pos
  have h2 : (Module.finrank ℚ E : ℝ) ≤ 2 * (padicValInt 2 (discr E) : ℝ) := by exact_mod_cast h1
  rw [GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds.delta_vp, le_div_iff₀ hn]
  linarith

end GlobalTheory.RootDiscrExp
