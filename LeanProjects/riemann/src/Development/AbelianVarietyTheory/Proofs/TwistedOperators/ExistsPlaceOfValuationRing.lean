import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow

open NumberField IsDedekindDomain Formalism.BasicNotions

namespace GlobalTheory.EmbeddingPlace

open NumberField IsDedekindDomain in
theorem _root_.GlobalTheory.EmbeddingPlace.finitePlace_le_one_iff {K : Type} [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K)) (x : K) :
    FinitePlace.mk v x ≤ 1 ↔ v.valuation K x ≤ 1 := by
  rw [FinitePlace.mk_apply, FinitePlace.norm_embedding, NumberField.HeightOneSpectrum.adicAbv_def,
    NNReal.coe_le_one]
  exact WithZeroMulInt.toNNReal_le_one_iff (NumberField.HeightOneSpectrum.one_lt_absNorm_nnreal v)

open NumberField IsDedekindDomain in
private theorem valuation_le_one_iff_exists_eq_mul_inv_of_notMem {R L : Type} [CommRing R] [IsDedekindDomain R]
    [Field L] [Algebra R L] [IsFractionRing R L] (v : HeightOneSpectrum R) (x : L) :
    v.valuation L x ≤ 1 ↔
      ∃ a, ∃ s ∉ v.asIdeal, x = algebraMap R L a * (algebraMap R L s)⁻¹ := by
  rw [← Valuation.mem_valuationSubring_iff,
    ← HeightOneSpectrum.valuationSubringAtPrime_eq_valuationSubring,
    ← ValuationSubring.mem_toSubring, HeightOneSpectrum.valuationSubringAtPrime_toSubring,
    Subalgebra.mem_toSubring]
  simp only [Localization.subalgebra.ofField]
  change (∃ a s, ∃ (_ : s ∈ v.asIdeal.primeCompl),
      x = algebraMap R L a * (algebraMap R L s)⁻¹) ↔ _
  exact ⟨fun ⟨a, s, hs, h⟩ => ⟨a, s, hs, h⟩, fun ⟨a, s, hs, h⟩ => ⟨a, s, hs, h⟩⟩

open NumberField IsDedekindDomain in
private theorem exists_heightOneSpectrum_range_iff_finitePlace_le_one {O : Type} [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] {K : Type} [Field K] [NumberField K] (p : ℕ) (hp : p ≠ 0)
    (hpO : (p : O) ∈ IsLocalRing.maximalIdeal O) (ι : K →+* FractionRing O) :
    ∃ la : HeightOneSpectrum (𝓞 K), (p : 𝓞 K) ∈ la.asIdeal ∧
      ∀ x : K, ι x ∈ (algebraMap O (FractionRing O)).range ↔ FinitePlace.mk la x ≤ 1 := by
  have hinj := IsFractionRing.injective O (FractionRing O)
  have hint : ∀ y : 𝓞 K, IsIntegral O (ι (algebraMap (𝓞 K) K y)) := fun y =>
    IsIntegral.map_of_comp_eq (algebraMap ℤ O) ι (RingHom.ext_int _ _)
      (RingOfIntegers.isIntegral_coe y)
  let ψ : 𝓞 K →+* O :=
    { toFun := fun y => IsIntegralClosure.mk' O (ι (algebraMap (𝓞 K) K y)) (hint y)
      map_one' := hinj (by simp [IsIntegralClosure.algebraMap_mk'])
      map_mul' := fun a b => hinj (by simp [IsIntegralClosure.algebraMap_mk'])
      map_zero' := hinj (by simp [IsIntegralClosure.algebraMap_mk'])
      map_add' := fun a b => hinj (by simp [IsIntegralClosure.algebraMap_mk']) }
  have hψ : ∀ y : 𝓞 K, algebraMap O (FractionRing O) (ψ y) = ι (algebraMap (𝓞 K) K y) :=
    fun y => IsIntegralClosure.algebraMap_mk' O _ (hint y)
  let P : Ideal (𝓞 K) := (IsLocalRing.maximalIdeal O).comap ψ
  have hpP : (p : 𝓞 K) ∈ P := Ideal.mem_comap.mpr (by rw [map_natCast]; exact hpO)
  have hPne : P ≠ ⊥ := by
    intro h
    have hp0 := hpP
    rw [h, Ideal.mem_bot, Nat.cast_eq_zero] at hp0
    exact hp hp0
  have hunitP : ∀ s : 𝓞 K, s ∉ P → IsUnit (ψ s) := fun s hs =>
    IsLocalRing.notMem_maximalIdeal.mp hs
  let la : HeightOneSpectrum (𝓞 K) :=
    { asIdeal := P, isPrime := Ideal.IsPrime.comap ψ, ne_bot := hPne }
  refine ⟨la, hpP, fun x => ?_⟩
  rw [_root_.GlobalTheory.EmbeddingPlace.finitePlace_le_one_iff]
  constructor
  · rintro ⟨o, ho⟩
    by_contra hx
    push_neg at hx
    have hx0 : x ≠ 0 := by
      rintro rfl
      simp at hx
    have hy : la.valuation K x⁻¹ < 1 := by
      rw [map_inv₀]
      exact inv_lt_one_of_one_lt₀ hx
    obtain ⟨a, s, hs, hxa⟩ := (valuation_le_one_iff_exists_eq_mul_inv_of_notMem la x⁻¹).mp hy.le
    have hs0 : algebraMap (𝓞 K) K s ≠ 0 := by
      have : s ≠ 0 := by
        rintro rfl
        exact hs (zero_mem _)
      exact (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 K) K)).mpr this
    have hsa : algebraMap (𝓞 K) K a = x⁻¹ * algebraMap (𝓞 K) K s := by
      rw [hxa, inv_mul_cancel_right₀ hs0]
    have hvs : la.valuation K (algebraMap (𝓞 K) K s) = 1 := by
      rw [HeightOneSpectrum.valuation_of_algebraMap]
      exact le_antisymm (la.intValuation_le_one s)
        (not_lt.mp fun h => hs ((la.intValuation_lt_one_iff_mem s).mp h))
    have hva : la.intValuation a < 1 := by
      rw [← HeightOneSpectrum.valuation_of_algebraMap (K := K)]
      change la.valuation K (algebraMap (𝓞 K) K a) < 1
      rw [hsa, map_mul, hvs, mul_one]
      exact hy
    have ha : ψ a ∈ IsLocalRing.maximalIdeal O :=
      Ideal.mem_comap.mp ((la.intValuation_lt_one_iff_mem a).mp hva)
    have heq : o * ψ a = ψ s := hinj (by
      rw [map_mul, ho, hψ, hψ, hsa, map_mul, ← mul_assoc, ← map_mul, mul_inv_cancel₀ hx0,
        map_one, one_mul])
    have hunit : IsUnit (o * ψ a) := by
      rw [heq]
      exact hunitP s hs
    exact (IsLocalRing.mem_maximalIdeal _).mp ha (isUnit_of_mul_isUnit_right hunit)
  · intro h
    obtain ⟨a, s, hs, rfl⟩ := (valuation_le_one_iff_exists_eq_mul_inv_of_notMem la x).mp h
    refine ⟨ψ a * ↑(hunitP s hs).unit⁻¹, ?_⟩
    rw [map_mul, map_units_inv, IsUnit.unit_spec, hψ, hψ, map_mul, map_inv₀]

open NumberField IsDedekindDomain in

theorem _root_.GlobalTheory.EmbeddingPlace.exists_place : ∀ (D : _root_.Formalism.BasicNotions.D7) (Ks : Type) [Field Ks] [NumberField Ks] (i : D.ntw.Tw) (ι : Ks →+* FractionRing (D.ntw.O i)), ∃ la : HeightOneSpectrum (𝓞 Ks), ((D.ntw.l i : ℕ) : 𝓞 Ks) ∈ la.asIdeal ∧ ∀ x : Ks, ι x ∈ (algebraMap (D.ntw.O i) (FractionRing (D.ntw.O i))).range ↔ FinitePlace.mk la x ≤ 1 := by
  intro D Ks _ _ i ι
  haveI := D.ntw.domO i
  haveI := D.ntw.dvrO i
  exact exists_heightOneSpectrum_range_iff_finitePlace_le_one (D.ntw.l i) (D.ntw.lPrime i).out.ne_zero (D.ntw.O_l i) ι

end GlobalTheory.EmbeddingPlace
