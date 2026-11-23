import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
open NumberField IsDedekindDomain Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host GlobalTheory.HeckeGal

noncomputable section

namespace GlobalTheory.TameRecPlace

theorem int_val_le_one {L Ω : Type} [Field L] [Field Ω] [Algebra L Ω] (A : ValuationSubring Ω) (x : 𝓞 L) :
    A.valuation (algebraMap L Ω (x : L)) ≤ 1 :=
  (A.valuation_le_one_iff _).mpr (mem_of_isIntegral_int A (x.isIntegral_coe.map (algebraMap L Ω).toIntAlgHom))

theorem intValuation_exp_neg_one {L : Type} [Field L] [NumberField L]
    (w : HeightOneSpectrum (𝓞 L)) (x : 𝓞 L) (h1 : x ∈ w.asIdeal) (h2 : x ∉ w.asIdeal ^ 2) :
    w.intValuation x = WithZero.exp (-1 : ℤ) := by
  have h0 : x ≠ 0 := by
    rintro rfl
    exact h2 (Submodule.zero_mem _)
  have ha : w.intValuation x ≤ WithZero.exp (-((1 : ℕ) : ℤ)) :=
    (w.intValuation_le_pow_iff_mem x 1).mpr (by simpa using h1)
  have hb : ¬ w.intValuation x ≤ WithZero.exp (-((2 : ℕ) : ℤ)) := fun h =>
    h2 ((w.intValuation_le_pow_iff_mem x 2).mp h)
  rw [w.intValuation_if_neg h0] at ha hb ⊢
  rw [WithZero.exp_le_exp] at ha hb
  rw [WithZero.exp_inj]
  omega

theorem one_lt_normV {E : Type} [Field E] [NumberField E] (v : HeightOneSpectrum (𝓞 E)) : 1 < normV v := by
  haveI : v.asIdeal.IsMaximal := v.isMaximal
  letI := Ideal.Quotient.field v.asIdeal
  exact Finite.one_lt_card

theorem main : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] (v : HeightOneSpectrum (𝓞 E))
    (A : ValuationSubring Ω), IsPlaceOver A v → ∀ (ϖ : 𝓞 E), ϖ ∈ v.asIdeal → ϖ ∉ v.asIdeal ^ 2 →
    ∀ (π : Ω) [FiniteDimensional E (IntermediateField.adjoin E {π})] [NumberField (IntermediateField.adjoin E {π})],
    π ^ (normV v - 1) = algebraMap E Ω (ϖ : E) →
    ∃ W : HeightOneSpectrum (𝓞 (IntermediateField.adjoin E {π})),
      W.asIdeal.comap (algebraMap (𝓞 E) (𝓞 (IntermediateField.adjoin E {π}))) = v.asIdeal ∧
      (∀ W' : HeightOneSpectrum (𝓞 (IntermediateField.adjoin E {π})),
        W'.asIdeal.comap (algebraMap (𝓞 E) (𝓞 (IntermediateField.adjoin E {π}))) = v.asIdeal → W' = W) ∧
      IsPlaceOver A W ∧ normV W = normV v ∧
      ∀ c : (W.adicCompletion (IntermediateField.adjoin E {π}))ˣ,
        (c : W.adicCompletion (IntermediateField.adjoin E {π})) =
          algebraMap (IntermediateField.adjoin E {π}) _ (IntermediateField.AdjoinSimple.gen E π) → IsUnifAt W c := by
  intro E Ω _ _ _ _ v A hA ϖ h1 h2 π _ _ hπ
  set K := IntermediateField.adjoin E {π} with hK
  have hn1 : 1 ≤ normV v - 1 := by have := one_lt_normV v; omega
  set n := normV v - 1 with hn

  set g : K := IntermediateField.AdjoinSimple.gen E π with hg
  have hgΩ : algebraMap K Ω g = π := IntermediateField.AdjoinSimple.algebraMap_gen E π
  have hgn : g ^ n = algebraMap E K (ϖ : E) := by
    apply (algebraMap K Ω).injective
    rw [map_pow, hgΩ, hπ]
    exact IsScalarTower.algebraMap_apply E K Ω _
  have hgint : IsIntegral ℤ g := by
    refine IsIntegral.of_pow (n := n) (by omega) ?_
    rw [hgn]
    exact ϖ.isIntegral_coe.map (algebraMap E K).toIntAlgHom
  set πO : 𝓞 K := ⟨g, hgint⟩ with hπO
  have hπOn : πO ^ n = algebraMap (𝓞 E) (𝓞 K) ϖ := by
    apply RingOfIntegers.ext
    show g ^ n = _
    rw [hgn]
    rfl
  have hϖ0 : ϖ ≠ 0 := by
    rintro rfl
    exact h2 (Submodule.zero_mem _)

  let f : 𝓞 K →+* A := ((algebraMap K Ω).comp (algebraMap (𝓞 K) K)).codRestrict A fun x =>
    (A.valuation_le_one_iff _).1 (int_val_le_one A x)
  have hf : ∀ x, x ∈ (IsLocalRing.maximalIdeal A).comap f ↔ A.valuation (algebraMap K Ω (x : K)) < 1 := fun x =>
    A.valuation_lt_one_iff (f x)
  have hπΩ : algebraMap K Ω ((πO : 𝓞 K) : K) = π := hgΩ
  have hAπ : A.valuation π < 1 := by
    have hv1 : A.valuation (algebraMap E Ω (ϖ : E)) < 1 := (hA ϖ).2 h1
    rw [← hπ, map_pow] at hv1
    by_contra hc
    exact (not_lt.2 (one_le_pow₀ (not_lt.1 hc))) hv1
  have hπmem : πO ∈ (IsLocalRing.maximalIdeal A).comap f := (hf πO).2 (by rw [hπΩ]; exact hAπ)
  have hπO0 : πO ≠ 0 := by
    intro h0
    have : πO ^ n = 0 := by rw [h0, zero_pow (by omega)]
    rw [hπOn] at this
    exact hϖ0 ((map_eq_zero_iff _ (FaithfulSMul.algebraMap_injective (𝓞 E) (𝓞 K))).1 this)
  let W : HeightOneSpectrum (𝓞 K) :=
    ⟨(IsLocalRing.maximalIdeal A).comap f, inferInstance, fun hb => hπO0 (by
      have := hπmem; rw [hb] at this; exact this)⟩
  have hWmem : ∀ x : 𝓞 K, x ∈ W.asIdeal ↔ A.valuation (algebraMap K Ω (x : K)) < 1 := hf
  have hWv : W.asIdeal.comap (algebraMap (𝓞 E) (𝓞 K)) = v.asIdeal := by
    ext x
    rw [Ideal.mem_comap, hWmem, ← hA x]
    have : ((algebraMap (𝓞 E) (𝓞 K) x : 𝓞 K) : K) = algebraMap E K (x : E) := rfl
    rw [this, ← IsScalarTower.algebraMap_apply]
  have hPW : IsPlaceOver A W := fun x => (hWmem x).symm

  haveI : v.asIdeal.IsMaximal := v.isMaximal
  haveI hLO : W.asIdeal.LiesOver v.asIdeal := ⟨hWv.symm⟩
  have hprW : Prime W.asIdeal := Ideal.prime_of_isPrime W.ne_bot W.isPrime
  have hconds : Prime v.asIdeal := Ideal.prime_of_isPrime v.ne_bot v.isPrime
  have hspan0 : Ideal.span {ϖ} ≠ ⊥ := by
    rw [Ne, Ideal.span_singleton_eq_bot]; exact hϖ0
  have hem := Ideal.IsDedekindDomain.emultiplicity_map_eq_ramificationIdx'_mul (R := 𝓞 E) (S := 𝓞 K)
    hspan0 hconds.irreducible hprW.irreducible W.ne_bot
  have hspan : (Ideal.span {ϖ}).map (algebraMap (𝓞 E) (𝓞 K)) = Ideal.span {πO} ^ n := by
    rw [Ideal.map_span, Set.image_singleton, ← hπOn, Ideal.span_singleton_pow]
  have hv1 : emultiplicity v.asIdeal (Ideal.span {ϖ}) = 1 := by
    rw [← Nat.cast_one, emultiplicity_eq_coe]
    refine ⟨?_, ?_⟩
    · rw [pow_one, Ideal.dvd_span_singleton]; exact h1
    · rw [Ideal.dvd_span_singleton]; exact h2
  rw [hspan, emultiplicity_pow hprW, hv1, mul_one] at hem
  set e := v.asIdeal.ramificationIdx' W.asIdeal with he
  set m := emultiplicity W.asIdeal (Ideal.span {πO}) with hm
  have hm1 : 1 ≤ m := by
    have := le_emultiplicity_of_pow_dvd (a := W.asIdeal) (b := Ideal.span {πO}) (k := 1)
      (by rw [pow_one]; exact Ideal.dvd_span_singleton.2 hπmem)
    simpa using this
  have hne : n ≤ e := by
    have : (n : ℕ∞) ≤ e := by
      rw [← hem]
      calc (n : ℕ∞) = n * 1 := (mul_one _).symm
        _ ≤ n * m := by gcongr
    exact_mod_cast this
  have hsum := Ideal.sum_ramification_inertia (R := 𝓞 E) (S := 𝓞 K) E K (p := v.asIdeal) v.ne_bot
  have hfin : Module.finrank E K ≤ n := by
    have hint : IsIntegral E π := by
      refine ⟨Polynomial.X ^ n - Polynomial.C (ϖ : E), ?_, ?_⟩
      · exact Polynomial.monic_X_pow_sub_C _ (by omega)
      · simp [hπ, Polynomial.eval₂_sub, Polynomial.eval₂_X_pow, Polynomial.eval₂_C]
    rw [IntermediateField.adjoin.finrank hint]
    have hd := minpoly.degree_le_of_ne_zero E π (p := Polynomial.X ^ n - Polynomial.C (ϖ : E))
      (Polynomial.X_pow_sub_C_ne_zero (by omega) _) (by simp [hπ])
    rw [Polynomial.degree_X_pow_sub_C (by omega)] at hd
    exact Polynomial.natDegree_le_of_degree_le hd
  have hWS : W.asIdeal ∈ IsDedekindDomain.primesOverFinset v.asIdeal (𝓞 K) :=
    (IsDedekindDomain.mem_primesOverFinset_iff v.ne_bot _).2 ⟨W.isPrime, hLO⟩
  have hpos : ∀ P ∈ IsDedekindDomain.primesOverFinset v.asIdeal (𝓞 K),
      1 ≤ v.asIdeal.ramificationIdx' P * v.asIdeal.inertiaDeg' P := by
    intro P hP
    obtain ⟨hPp, hPl⟩ := (IsDedekindDomain.mem_primesOverFinset_iff v.ne_bot _).1 hP
    have h1' : v.asIdeal.ramificationIdx' P ≠ 0 := by
      refine Ideal.IsDedekindDomain.ramificationIdx'_ne_zero (Ideal.map_ne_bot_of_ne_bot v.ne_bot) hPp ?_
      rw [Ideal.map_le_iff_le_comap]
      exact (Ideal.LiesOver.over (P := P) (p := v.asIdeal)).le
    have h2' : 0 < v.asIdeal.inertiaDeg' P := Ideal.inertiaDeg'_pos v.asIdeal P
    exact Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero h1' h2'.ne')
  rw [← Finset.add_sum_erase _ _ hWS] at hsum
  change e * v.asIdeal.inertiaDeg' W.asIdeal + _ = _ at hsum
  have hfW : 0 < v.asIdeal.inertiaDeg' W.asIdeal := Ideal.inertiaDeg'_pos v.asIdeal W.asIdeal
  have hrest : ∀ P ∈ (IsDedekindDomain.primesOverFinset v.asIdeal (𝓞 K)).erase W.asIdeal, False := by
    intro P hP
    have hle := Finset.single_le_sum (f := fun P => v.asIdeal.ramificationIdx' P * v.asIdeal.inertiaDeg' P)
      (fun _ _ => Nat.zero_le _) hP
    have := hpos P (Finset.mem_of_mem_erase hP)
    have : e * 1 ≤ e * v.asIdeal.inertiaDeg' W.asIdeal := Nat.mul_le_mul_left _ hfW
    omega
  have hsum0 : ∑ P ∈ (IsDedekindDomain.primesOverFinset v.asIdeal (𝓞 K)).erase W.asIdeal,
      v.asIdeal.ramificationIdx' P * v.asIdeal.inertiaDeg' P = 0 :=
    Finset.sum_eq_zero fun P hP => (hrest P hP).elim
  rw [hsum0, add_zero] at hsum
  have hen : e = n ∧ v.asIdeal.inertiaDeg' W.asIdeal = 1 := by
    have : e * 1 ≤ e * v.asIdeal.inertiaDeg' W.asIdeal := Nat.mul_le_mul_left _ hfW
    have h3 : e * v.asIdeal.inertiaDeg' W.asIdeal ≤ n := hsum ▸ hfin
    refine ⟨by omega, ?_⟩
    have he0 : 0 < e := by omega
    by_contra hc
    have : e * 2 ≤ e * v.asIdeal.inertiaDeg' W.asIdeal := Nat.mul_le_mul_left _ (by omega)
    omega

  obtain ⟨hen, hf1⟩ := hen
  have hπ2 : πO ∉ W.asIdeal ^ 2 := by
    intro h
    have h2m : ((2 : ℕ) : ℕ∞) ≤ m := le_emultiplicity_of_pow_dvd (Ideal.dvd_span_singleton.2 h)
    have : ((n * 2 : ℕ) : ℕ∞) ≤ (e : ℕ∞) := by
      rw [← hem, Nat.cast_mul]
      gcongr
    have := (Nat.cast_le.1 this)
    omega
  refine ⟨W, hWv, ?_, hPW, ?_, ?_⟩
  · intro W' hW'
    have hmem : W'.asIdeal ∈ IsDedekindDomain.primesOverFinset v.asIdeal (𝓞 K) :=
      (IsDedekindDomain.mem_primesOverFinset_iff v.ne_bot _).2 ⟨W'.isPrime, ⟨hW'.symm⟩⟩
    by_contra hne'
    have hne2 : W'.asIdeal ≠ W.asIdeal := fun h => hne' (HeightOneSpectrum.ext h)
    exact hrest _ (Finset.mem_erase.2 ⟨hne2, hmem⟩)
  · letI := Ideal.Quotient.field v.asIdeal
    have hfr : Module.finrank (𝓞 E ⧸ v.asIdeal) (𝓞 K ⧸ W.asIdeal) = 1 := by
      rw [← Ideal.inertiaDeg'_algebraMap]; exact hf1
    show Nat.card (𝓞 K ⧸ W.asIdeal) = Nat.card (𝓞 E ⧸ v.asIdeal)
    rw [Module.natCard_eq_pow_finrank (K := 𝓞 E ⧸ v.asIdeal), hfr, pow_one]
  · intro c hc
    show Valued.v (c : W.adicCompletion K) = WithZero.exp (-1)
    rw [hc]
    have h3 : Valued.v (((πO : 𝓞 K) : K) : W.adicCompletion K) = W.valuation K ((πO : 𝓞 K) : K) :=
      HeightOneSpectrum.valuedAdicCompletion_eq_valuation' W _
    have h4 : W.valuation K ((πO : 𝓞 K) : K) = WithZero.exp (-1) := by
      rw [show ((πO : 𝓞 K) : K) = algebraMap (𝓞 K) K πO from rfl, HeightOneSpectrum.valuation_of_algebraMap]
      exact intValuation_exp_neg_one W πO hπmem hπ2
    rw [← h4, ← h3]
    rfl

end GlobalTheory.TameRecPlace
