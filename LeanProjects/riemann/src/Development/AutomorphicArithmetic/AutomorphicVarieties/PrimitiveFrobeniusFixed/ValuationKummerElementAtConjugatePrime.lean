import Development.AutomorphicArithmetic.AutomorphicVarieties.PrimitiveFrobeniusFixed.IsAdmissiblePrimeListNil
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.StickelbergerTheorem.ImportsBis
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.StickelbergerTheorem.SplitInj
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.StickelbergerTheorem.SplitProd

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base UpperTheory.V.Odd UpperTheory.V.Stick UpperTheory.V.ML
open scoped nonZeroDivisors Pointwise

private theorem val_int {E : Type} [Field E] [NumberField E] (v : HeightOneSpectrum (𝓞 E)) {r : 𝓞 E} (hr : r ≠ 0) :
    v.valuation E (algebraMap (𝓞 E) E r) = WithZero.exp (-FractionalIdeal.count E v
      (FractionalIdeal.spanSingleton (𝓞 E)⁰ (algebraMap (𝓞 E) E r))) := by
  classical
  have hr' : algebraMap (𝓞 E) E r ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 E) E)).mpr hr
  have hI : FractionalIdeal.spanSingleton (𝓞 E)⁰ (algebraMap (𝓞 E) E r) ≠ 0 := by
    rw [Ne, FractionalIdeal.spanSingleton_eq_zero_iff]
    exact hr'
  have h : FractionalIdeal.spanSingleton (𝓞 E)⁰ (algebraMap (𝓞 E) E r) =
      FractionalIdeal.spanSingleton (𝓞 E)⁰ ((algebraMap (𝓞 E) E 1)⁻¹) * ↑(Ideal.span {r}) := by
    rw [map_one, inv_one, FractionalIdeal.spanSingleton_one, one_mul,
      FractionalIdeal.coeIdeal_span_singleton]
  rw [FractionalIdeal.count_well_defined E v hI h, HeightOneSpectrum.valuation_of_algebraMap,
    v.intValuation_if_neg hr, Ideal.span_singleton_one, ← Ideal.one_eq_top, Associates.mk_one,
    Associates.factors_one, Associates.count_zero v.associates_irreducible]
  simp

private theorem val_count {E : Type} [Field E] [NumberField E] (v : HeightOneSpectrum (𝓞 E)) {α : E} (hα : α ≠ 0) :
    v.valuation E α = WithZero.exp (-FractionalIdeal.count E v
      (FractionalIdeal.spanSingleton (𝓞 E)⁰ α)) := by
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (𝓞 E) α
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  have ha0 : a ≠ 0 := by
    rintro rfl
    simp at hα
  have hb' : algebraMap (𝓞 E) E b ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 E) E)).mpr hb0
  have ha' : algebraMap (𝓞 E) E a ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 E) E)).mpr ha0
  have hIa : FractionalIdeal.spanSingleton (𝓞 E)⁰ (algebraMap (𝓞 E) E a) ≠ 0 := by
    rw [Ne, FractionalIdeal.spanSingleton_eq_zero_iff]
    exact ha'
  have hIb : (FractionalIdeal.spanSingleton (𝓞 E)⁰ (algebraMap (𝓞 E) E b))⁻¹ ≠ 0 := by
    rw [Ne, inv_eq_zero, FractionalIdeal.spanSingleton_eq_zero_iff]
    exact hb'
  rw [div_eq_mul_inv, ← FractionalIdeal.spanSingleton_mul_spanSingleton, ← FractionalIdeal.spanSingleton_inv,
    FractionalIdeal.count_mul E v hIa hIb, FractionalIdeal.count_inv, map_mul, map_inv₀,
    val_int v ha0, val_int v hb0, neg_add, neg_neg, WithZero.exp_add]
  simp [WithZero.exp_neg]

private theorem count_fam {E ι : Type} [Field E] [NumberField E] [Fintype ι]
    (P : ι → HeightOneSpectrum (𝓞 E)) (hP : Function.Injective P) (k : ι → ℤ) (t : ι) :
    FractionalIdeal.count E (P t) (∏ s, (((P s).asIdeal : FractionalIdeal (𝓞 E)⁰ E)) ^ k s) = k t := by
  classical
  rw [FractionalIdeal.count_prod E (P t) _ _ fun s _ =>
    zpow_ne_zero _ (FractionalIdeal.coeIdeal_ne_zero.2 (P s).ne_bot)]
  rw [Finset.sum_eq_single t]
  · exact FractionalIdeal.count_zpow_self E (P t) _
  · intro s _ hs
    rw [FractionalIdeal.count_zpow, FractionalIdeal.count_maximal_coprime E (P t) fun h => hs (hP h), mul_zero]
  · intro h
    exact absurd (Finset.mem_univ t) h

theorem UpperTheory.valuation_kummerElement_at_conjugate_prime :
    ∀ (M : ℕ) [NeZero M] (K : Type) [Field K] [NumberField K] [IsCyclotomicExtension {M} ℚ K] (b r : ℕ) (v w : HeightOneSpectrum (𝓞 K)) (X : K) (t : (ZMod M)ˣ), r.Prime → r ≡ 1 [MOD M] → IsX M K b v.asIdeal X → (r : 𝓞 K) ∈ v.asIdeal → w.asIdeal = conjI M K v.asIdeal t → w.valuation K X = w.valuation K (r : K) ^ th M b t := by
  intro M _ K _ _ _ b r v w X t hr hr1 hX hrv hw
  haveI : Fact r.Prime := ⟨hr⟩
  have hndvd : ¬ r ∣ M := by
    intro hd
    have h1 : M ∣ r - 1 := (Nat.modEq_iff_dvd' hr.one_le).mp hr1.symm
    have h2 : r ∣ r - 1 := Nat.dvd_trans hd h1
    have h3 : 0 < r - 1 := by have := hr.two_le; omega
    have := Nat.le_of_dvd h3 h2
    have := hr.two_le
    omega
  have hcop : r.Coprime M := (Nat.Prime.coprime_iff_not_dvd hr).mpr hndvd
  haveI hlies : v.asIdeal.LiesOver (Ideal.span {(r : ℤ)}) := by
    constructor
    have hmax : (Ideal.span {(r : ℤ)}).IsMaximal :=
      ((Ideal.span_singleton_prime (by exact_mod_cast hr.ne_zero)).mpr
        (Nat.prime_iff_prime_int.mp hr)).isMaximal (by simp [hr.ne_zero])
    refine hmax.eq_of_le (Ideal.IsPrime.comap _).ne_top ?_
    rw [Ideal.span_le, Set.singleton_subset_iff]
    show algebraMap ℤ (𝓞 K) (r : ℤ) ∈ v.asIdeal
    simpa using hrv
  have hdeg : v.asIdeal.inertiaDeg ℤ = 1 := by
    rw [IsCyclotomicExtension.Rat.inertiaDeg_eq_of_not_dvd r K v.asIdeal hndvd]
    have : (r : ZMod M) = 1 := by
      have := (ZMod.natCast_eq_natCast_iff r 1 M).mpr hr1
      simpa using this
    rw [this, orderOf_one]
  have hnorm : Ideal.absNorm v.asIdeal = r := by
    rw [← Ideal.absNorm_pow_inertiaDeg (Ideal.span {(r : ℤ)}) v.asIdeal, hdeg, pow_one]
    simp [Ideal.absNorm_span_singleton]
  obtain ⟨π, hπ⟩ := (red K r v.asIdeal).1 hnorm
  obtain ⟨hprime, hprod⟩ := splitProd M K r π hcop
  have hinj := splitInj M K r π hcop
  rw [hπ] at hprime hprod hinj
  let fam : (ZMod M)ˣ → HeightOneSpectrum (𝓞 K) := fun s =>
    ⟨conjI M K v.asIdeal s, Ideal.isPrime_of_prime (hprime s), (hprime s).ne_zero⟩
  have hfam : Function.Injective fam := by
    intro s s' h
    exact hinj (congrArg HeightOneSpectrum.asIdeal h)
  obtain rfl : w = fam t := HeightOneSpectrum.ext hw
  have hX0 : X ≠ 0 := left_ne_zero_of_mul_eq_one hX.1
  have hr0 : (r : 𝓞 K) ≠ 0 := by exact_mod_cast hr.ne_zero
  have hrK : (r : K) = algebraMap (𝓞 K) K (r : 𝓞 K) := by simp
  rw [val_count (fam t) hX0, hX.2, hrK, val_int (fam t) hr0,
    ← FractionalIdeal.coeIdeal_span_singleton, ← hprod]
  have hcoe : ((∏ s, conjI M K v.asIdeal s : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K) =
      ∏ s, (((fam s).asIdeal : FractionalIdeal (𝓞 K)⁰ K)) ^ ((fun _ => (1 : ℤ)) s) := by
    simp only [zpow_one]
    exact map_prod (FractionalIdeal.coeIdealHom (𝓞 K)⁰ K) _ _
  have hX2 : (∏ s, ((conjI M K v.asIdeal s : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K) ^ th M b (s : ZMod M)) =
      ∏ s, (((fam s).asIdeal : FractionalIdeal (𝓞 K)⁰ K)) ^ ((fun s : (ZMod M)ˣ => th M b (s : ZMod M)) s) := rfl
  rw [hcoe, hX2, count_fam fam hfam, count_fam fam hfam, ← WithZero.exp_zsmul]
  simp
