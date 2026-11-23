import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ConjugateOrderData
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.PadicValNatAbsNormEqZero

noncomputable section

open NumberField IsDedekindDomain GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations UniqueFactorizationMonoid

namespace GlobalTheory.DifferentElement

theorem exists_intLift (E : Type) [Field E] [NumberField E] (V : Type) [CommRing V] [IsDomain V] [IsIntegrallyClosed V]
    (k : Type) [Field k] [Algebra V k] [IsFractionRing V k] (ψ : E →+* k) :
    ∃ σ : 𝓞 E →+* V, ∀ x : 𝓞 E, algebraMap V k (σ x) = ψ (x : E) := by
  have hinj : Function.Injective (algebraMap V k) := IsFractionRing.injective V k
  have h : ∀ x : 𝓞 E, ∃ v : V, algebraMap V k v = ψ (x : E) := by
    intro x
    apply IsIntegrallyClosed.algebraMap_eq_of_integral
    have h1 : IsIntegral ℤ (ψ (x : E)) := (RingOfIntegers.isIntegral_coe x).map ψ.toIntAlgHom
    exact h1.tower_top
  choose s hs using h
  refine ⟨{ toFun := s, map_one' := hinj ?_, map_mul' := fun x y => hinj ?_,
            map_zero' := hinj ?_, map_add' := fun x y => hinj ?_ }, hs⟩
  · rw [hs]; simp
  · rw [map_mul, hs, hs, hs]; simp
  · rw [hs]; simp
  · rw [map_add, hs, hs, hs]; simp

theorem ord_vw_pow_mul_unit (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (K : Type) [Field K]
    [Algebra O K] [IsFractionRing O K] {ϖ : O} (hϖ : Irreducible ϖ) (u : Oˣ) (n : ℕ) :
    ord_vw O (algebraMap O K (ϖ ^ n * u)) = n := by
  have h1 : (IsDiscreteValuationRing.maximalIdeal O).valuation K (algebraMap O K (u : O)) = 1 := by
    rw [HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.intValuation_eq_one_iff]
    exact fun h => (IsLocalRing.mem_maximalIdeal _).1 h u.isUnit
  have h2 : (IsDiscreteValuationRing.maximalIdeal O).valuation K (algebraMap O K ϖ) = WithZero.exp (-1) := by
    rw [HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.intValuation_singleton _ hϖ.ne_zero
      ((IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).1 hϖ)]
  unfold ord_vw
  rw [map_mul, map_pow, map_mul, map_pow, h1, h2, mul_one, ← WithZero.exp_nsmul, WithZero.log_exp]
  simp

end GlobalTheory.DifferentElement

namespace GlobalTheory.DifferentElement

theorem exists_pow_mul_unit {E : Type} [Field E] [NumberField E] {O : Type} [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] (ι : 𝓞 E →+* O) (hQ0 : Ideal.comap ι (IsLocalRing.maximalIdeal O) ≠ ⊥) {ϖ : O} (e : ℕ)
    (he : Ideal.map ι (Ideal.comap ι (IsLocalRing.maximalIdeal O)) = Ideal.span {ϖ ^ e}) (z : 𝓞 E) (hz : z ≠ 0) :
    ∃ u : Oˣ, ι z = ϖ ^ (e * multiplicity (Ideal.comap ι (IsLocalRing.maximalIdeal O)) (Ideal.span {z})) * u := by
  set Q := Ideal.comap ι (IsLocalRing.maximalIdeal O) with hQdef
  have hQp : Q.IsPrime := Ideal.comap_isPrime ι _
  set k := multiplicity Q (Ideal.span {z})
  have hz0 : Ideal.span {z} ≠ ⊥ := by rwa [Ne, Ideal.span_singleton_eq_bot]
  have hfin : FiniteMultiplicity Q (Ideal.span {z}) :=
    FiniteMultiplicity.of_prime_left (Ideal.prime_of_isPrime hQ0 hQp) hz0
  obtain ⟨J, hJ⟩ := pow_multiplicity_dvd Q (Ideal.span {z})
  have hJQ : ¬ J ≤ Q := by
    intro hle
    have : Q ^ (k + 1) ∣ Ideal.span {z} := by
      rw [hJ, pow_succ]
      exact mul_dvd_mul_left _ (Ideal.dvd_iff_le.2 hle)
    exact (hfin.pow_dvd_iff_le_multiplicity.1 this).not_gt (Nat.lt_succ_self k)
  obtain ⟨s, hsJ, hsQ⟩ := SetLike.not_le_iff_exists.1 hJQ
  have hsu : IsUnit (ι s) := by
    by_contra h
    exact hsQ (Ideal.mem_comap.2 ((IsLocalRing.mem_maximalIdeal _).2 h))
  have hJt : Ideal.map ι J = ⊤ := Ideal.eq_top_of_isUnit_mem _ (Ideal.mem_map_of_mem ι hsJ) hsu
  have h1 : Ideal.span {ι z} = Ideal.span {ϖ ^ (e * k)} := by
    rw [← Set.image_singleton, ← Ideal.map_span, hJ, Ideal.map_mul, Ideal.map_pow, he, hJt, Ideal.mul_top,
      Ideal.span_singleton_pow, pow_mul]
  obtain ⟨u, hu⟩ := (Ideal.span_singleton_eq_span_singleton.1 h1).symm
  exact ⟨u, hu.symm⟩

theorem mult_ratio (E : Type) [Field E] [NumberField E] [IsGalois ℚ E] (l : ℕ) (hl : l.Prime) (P : Ideal (𝓞 E))
    (hP : P.IsPrime) (hlP : (l : 𝓞 E) ∈ P) :
    (multiplicity P (differentIdeal ℤ (𝓞 E)) : ℚ) / (multiplicity P (Ideal.span {(l : 𝓞 E)}) : ℚ) =
      ((discr E).natAbs.factorization l : ℚ) / (Module.finrank ℚ E : ℚ) := by
  classical
  have hl0 : (l : 𝓞 E) ≠ 0 := Nat.cast_ne_zero.2 hl.ne_zero
  have hP0 : P ≠ ⊥ := by
    rintro rfl
    exact hl0 ((Submodule.mem_bot _).1 hlP)
  have hirr : Irreducible P := (Ideal.prime_of_isPrime hP0 hP).irreducible
  have hd : (discr E).natAbs ≠ 0 := Int.natAbs_ne_zero.mpr (discr_ne_zero E)
  have h := ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.diffExp E l ((discr E).natAbs.factorization l) (ordCompl[l] (discr E).natAbs) hl
    (Nat.not_dvd_ordCompl hl hd) (Nat.ordProj_mul_ordCompl_eq_self _ _).symm P hP hlP
  have hspan0 : Ideal.span {(l : 𝓞 E)} ≠ ⊥ := by rwa [Ne, Ideal.span_singleton_eq_bot]
  have hpos := ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.count_span_pos E l hl hP hlP
  rw [multiplicity_eq_count_normalizedFactors hirr differentIdeal_ne_bot,
    multiplicity_eq_count_normalizedFactors hirr hspan0, normalize_eq]
  have hn : (Module.finrank ℚ E : ℚ) ≠ 0 := Nat.cast_ne_zero.2 Module.finrank_pos.ne'
  rw [div_eq_div_iff (by exact_mod_cast hpos.ne') hn]
  convert congrArg (fun t : ℕ => (t : ℚ)) h using 1 <;> push_cast <;> ring

end GlobalTheory.DifferentElement

namespace GlobalTheory.DifferentElement

open Classical in

theorem diff_element : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [IsGalois ℚ E] (l : ℕ), l.Prime →
    ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O] (K : Type) [Field K] [Algebra O K]
    [IsFractionRing O K], (l : O) ∈ IsLocalRing.maximalIdeal O → Nat.card (E →+* K) = Module.finrank ℚ E →
    ∃ D : O, (∀ P : HeightOneSpectrum (𝓞 E), (l : 𝓞 E) ∈ P.asIdeal →
        val_vp O l (algebraMap O K D) = ((diffExp_vp l P : ℚ) : WithTop ℚ)) ∧
      ∀ (σ : E →+* K) (y : E), (∀ x : 𝓞 E, ∃ n : ℤ, Algebra.trace ℚ E (y * x) = n) →
        ∃ z : O, algebraMap O K z = algebraMap O K D * σ y := by
  intro E _ _ _ _ l hl O _ _ _ _ K _ _ _ hlm hcard
  have hne : Nonempty (E →+* K) := by
    have : 0 < Nat.card (E →+* K) := hcard ▸ Module.finrank_pos
    exact (Nat.card_pos_iff.1 this).1
  obtain ⟨σ0⟩ := hne
  obtain ⟨ι, hι⟩ := exists_intLift E O K σ0
  set Q := Ideal.comap ι (IsLocalRing.maximalIdeal O) with hQdef
  have hlQ : (l : 𝓞 E) ∈ Q := by rw [Ideal.mem_comap, map_natCast]; exact hlm
  have hl0 : (l : 𝓞 E) ≠ 0 := Nat.cast_ne_zero.2 hl.ne_zero
  have hlO : (l : O) ≠ 0 := Nat.cast_ne_zero.2 hl.ne_zero
  have hQ0 : Q ≠ ⊥ := by
    intro h
    rw [h] at hlQ
    exact hl0 ((Submodule.mem_bot _).1 hlQ)
  have hQp : Q.IsPrime := Ideal.comap_isPrime ι _
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  have hmap0 : Ideal.map ι Q ≠ ⊥ := by
    intro h
    have := Ideal.mem_map_of_mem ι hlQ
    rw [h, map_natCast] at this
    exact hlO ((Submodule.mem_bot _).1 this)
  obtain ⟨e, he⟩ := IsDiscreteValuationRing.ideal_eq_span_pow_irreducible hmap0 hϖ
  have he0 : e ≠ 0 := by
    rintro rfl
    rw [pow_zero, Ideal.span_singleton_one] at he
    exact (IsLocalRing.maximalIdeal.isMaximal O).ne_top (top_le_iff.1 (he ▸ Ideal.map_comap_le))

  set 𝔇 := differentIdeal ℤ (𝓞 E) with h𝔇def
  have h𝔇 : 𝔇 ≠ ⊥ := differentIdeal_ne_bot
  have hfin𝔇 : FiniteMultiplicity Q 𝔇 := FiniteMultiplicity.of_prime_left (Ideal.prime_of_isPrime hQ0 hQp) h𝔇
  set k := multiplicity Q 𝔇 with hkdef
  have hnle : ¬ 𝔇 ≤ Q ^ (k + 1) := fun h =>
    (hfin𝔇.pow_dvd_iff_le_multiplicity.1 (Ideal.dvd_iff_le.2 h)).not_gt (Nat.lt_succ_self k)
  obtain ⟨x, hx𝔇, hxQ⟩ := SetLike.not_le_iff_exists.1 hnle
  have hx0 : x ≠ 0 := by
    rintro rfl
    exact hxQ (zero_mem _)
  have hxk : multiplicity Q (Ideal.span {x}) = k := by
    refine multiplicity_eq_of_dvd_of_not_dvd ?_ ?_
    · exact Ideal.dvd_iff_le.2 (((Ideal.span_singleton_le_iff_mem _).2 hx𝔇).trans
        (Ideal.le_of_dvd (pow_multiplicity_dvd Q 𝔇)))
    · intro h
      exact hxQ ((Ideal.span_singleton_le_iff_mem _).1 (Ideal.le_of_dvd h))
  refine ⟨ι x, ?_, ?_⟩
  · intro P hP
    obtain ⟨u, hu⟩ := exists_pow_mul_unit ι hQ0 e he x hx0
    obtain ⟨u', hu'⟩ := exists_pow_mul_unit ι hQ0 e he (l : 𝓞 E) hl0
    have hxK : algebraMap O K (ι x) ≠ 0 := by
      rw [map_ne_zero_iff _ (IsFractionRing.injective O K), hu]
      exact mul_ne_zero (pow_ne_zero _ hϖ.ne_zero) u.ne_zero
    have hlK : (l : K) = algebraMap O K (ι (l : 𝓞 E)) := by rw [map_natCast, map_natCast]
    rw [val_vp, if_neg hxK, hlK, hu, hu', ord_vw_pow_mul_unit O K hϖ, ord_vw_pow_mul_unit O K hϖ, hxk]
    congr 1
    have hr1 := mult_ratio E l hl P.asIdeal P.isPrime hP
    have hr2 := mult_ratio E l hl Q hQp hlQ
    rw [diffExp_vp, hr1, ← hr2]
    have hkl : multiplicity Q (Ideal.span {(l : 𝓞 E)}) ≠ 0 := by
      have hfl : FiniteMultiplicity Q (Ideal.span {(l : 𝓞 E)}) := FiniteMultiplicity.of_prime_left
        (Ideal.prime_of_isPrime hQ0 hQp) (by rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]; exact hl0)
      have := hfl.le_multiplicity_of_pow_dvd (k := 1) (by
        rw [pow_one]; exact Ideal.dvd_iff_le.2 ((Ideal.span_singleton_le_iff_mem _).2 hlQ))
      omega
    push_cast
    rw [mul_div_mul_left _ _ (by exact_mod_cast he0)]
  · intro σ y hy
    haveI : CharZero K := charZero_of_injective_ringHom σ0.injective
    letI : Algebra E K := σ0.toAlgebra
    haveI : IsScalarTower ℚ E K := IsScalarTower.of_algebraMap_eq fun q => by
      show algebraMap ℚ K q = σ0 (algebraMap ℚ E q)
      rw [eq_ratCast (algebraMap ℚ K), eq_ratCast (algebraMap ℚ E), map_ratCast]
    let τ : E ≃ₐ[ℚ] E := (σ.toRatAlgHom).restrictNormal' E
    have hτ : ∀ w, σ0 (τ w) = σ w := fun w => (σ.toRatAlgHom).restrictNormal_commutes E w
    have hyd : y ∈ Submodule.traceDual ℤ ℚ (1 : Submodule (𝓞 E) E) := by
      rw [Submodule.mem_traceDual]
      intro a ha
      obtain ⟨b, rfl⟩ := Submodule.mem_one.1 ha
      obtain ⟨n, hn⟩ := hy b
      exact ⟨n, by rw [Algebra.traceForm_apply, eq_intCast]; exact hn.symm⟩
    have hτy := ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.traceDual_smul τ hyd
    have hx' := (ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.mem_differentIdeal_iff x).1 hx𝔇
    rw [Submodule.mem_div_iff_forall_mul_mem] at hx'
    obtain ⟨b, hb⟩ := Submodule.mem_one.1 (hx' _ hτy)
    refine ⟨ι b, ?_⟩
    rw [hι, hι, ← hτ, ← map_mul]
    exact congrArg σ0 hb

end GlobalTheory.DifferentElement
