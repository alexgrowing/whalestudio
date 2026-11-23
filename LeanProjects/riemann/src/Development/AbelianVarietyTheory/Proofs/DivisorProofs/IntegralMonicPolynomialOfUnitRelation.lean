import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsNormEqFixedUnitHenselian
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PadicIntegersHenselianFiniteResidue
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FiniteMaximalSpectrumOfFiniteOfIsLocalRing
open scoped TensorProduct
open IsLocalRing IsDedekindDomain IsDedekindDomain.HeightOneSpectrum

namespace GlobalTheory.OddLocalNorm

theorem exists_eq_of_finite (O : Type) {S : Type} [CommRing O] [HenselianLocalRing O]
    [Finite (ResidueField O)] [CommRing S] [Algebra O S] [Module.Finite O S]
    (h2 : IsUnit (2 : O)) {m d : S} (hm : IsUnit m) (hd : IsUnit d) :
    ∃ a b : S, m = a * a - d * (b * b) := by
  let T := QuadraticAlgebra S d 0
  haveI : Module.Finite O T := Module.Finite.trans S T
  let I : Ideal T := (maximalIdeal O).map (algebraMap O T)
  have hI : I ≤ (⊥ : Ideal T).jacobson := by
    refine le_sInf fun M hM => Ideal.map_le_iff_le_comap.2 ?_
    haveI := hM.2
    exact (eq_maximalIdeal (Ideal.isMaximal_comap_of_isIntegral_of_isMaximal (R := O) M)).ge
  haveI : HenselianRing T I := GlobalTheory.henselianRing_of_finite O I hI
  haveI : Finite (O ⧸ maximalIdeal O) := inferInstanceAs (Finite (ResidueField O))
  haveI : Module.Finite O (T ⧸ I) :=
    Module.Finite.of_surjective (Ideal.Quotient.mkₐ O I).toLinearMap Ideal.Quotient.mk_surjective
  haveI : Module.Finite (O ⧸ maximalIdeal O) (T ⧸ I) :=
    Module.Finite.of_restrictScalars_finite O _ _
  haveI : Finite (T ⧸ I) := Module.finite_of_finite (O ⧸ maximalIdeal O)
  have hc : ∀ s : S, starRingEnd T (algebraMap S T s) = algebraMap S T s := by
    intro s
    ext <;> simp [T, starRingEnd_apply]
  have hcO : (starRingEnd T).comp (algebraMap O T) = algebraMap O T := by
    ext1 r
    rw [RingHom.comp_apply, IsScalarTower.algebraMap_apply O S T, hc]
  have hcI : I ≤ I.comap (starRingEnd T) := by
    rw [Ideal.map_le_iff_le_comap, Ideal.comap_comap, hcO]
    exact Ideal.le_comap_map
  have h2S : IsUnit (2 : S) := by
    simpa only [map_ofNat] using h2.map (algebraMap O S)
  obtain ⟨x, hx⟩ := GlobalTheory.HenselianNorm.exists_norm_eq T I (starRingEnd T)
    (fun x => star_star x) (fun x hx => hcI hx)
    ⟨⟨0, 1⟩, by
      have h : ((⟨0, 1⟩ : T) - starRingEnd T ⟨0, 1⟩) * ((⟨0, 1⟩ : T) - starRingEnd T ⟨0, 1⟩)
          = algebraMap S T (2 * 2 * d) := by
        ext <;> simp [T, starRingEnd_apply]
        ring
      exact isUnit_of_mul_isUnit_left (h ▸ ((h2S.mul h2S).mul hd).map (algebraMap S T))⟩
    (algebraMap S T m) (hc m) (hm.map _)
  refine ⟨x.re, x.im, ?_⟩
  have := congrArg QuadraticAlgebra.re hx
  simp [T, starRingEnd_apply] at this
  linear_combination -this

theorem exists_eq_of_isIntegral (O : Type) {A : Type} [CommRing O] [HenselianLocalRing O]
    [Finite (ResidueField O)] [CommRing A] [Algebra O A]
    (h2 : IsUnit (2 : O)) {m m' d d' : A} (hm : m * m' = 1) (hd : d * d' = 1)
    (im : IsIntegral O m) (im' : IsIntegral O m') (id : IsIntegral O d) (id' : IsIntegral O d') :
    ∃ a b : A, m = a * a - d * (b * b) := by
  let S := Algebra.adjoin O ({m, m', d, d'} : Set A)
  haveI : Module.Finite O S := Algebra.finite_adjoin_of_finite_of_isIntegral (Set.toFinite _) (by
    rintro x (rfl | rfl | rfl | rfl) <;> assumption)
  have h1 : m ∈ S := Algebra.subset_adjoin (by simp)
  have h1' : m' ∈ S := Algebra.subset_adjoin (by simp)
  have h3 : d ∈ S := Algebra.subset_adjoin (by simp)
  have h3' : d' ∈ S := Algebra.subset_adjoin (by simp)
  obtain ⟨a, b, h⟩ := exists_eq_of_finite O h2 (m := (⟨m, h1⟩ : S)) (d := ⟨d, h3⟩)
    (IsUnit.of_mul_eq_one ⟨m', h1'⟩ (Subtype.ext hm)) (IsUnit.of_mul_eq_one ⟨d', h3'⟩ (Subtype.ext hd))
  exact ⟨a, b, congrArg Subtype.val h⟩

theorem exists_eq_sq_sub_mul_sq : ∀ (L : Type) [Field L] [NumberField L] (v : IsDedekindDomain.HeightOneSpectrum ℤ), v.asIdeal ≠ Ideal.span {2} →
    ∀ m m' d d' : v.adicCompletion ℚ ⊗[ℚ] L, m * m' = 1 → d * d' = 1 →
    (∃ f : Polynomial (v.adicCompletion ℚ), f.Monic ∧ (∀ i, f.coeff i ∈ v.adicCompletionIntegers ℚ) ∧ Polynomial.aeval m f = 0) →
    (∃ f : Polynomial (v.adicCompletion ℚ), f.Monic ∧ (∀ i, f.coeff i ∈ v.adicCompletionIntegers ℚ) ∧ Polynomial.aeval m' f = 0) →
    (∃ f : Polynomial (v.adicCompletion ℚ), f.Monic ∧ (∀ i, f.coeff i ∈ v.adicCompletionIntegers ℚ) ∧ Polynomial.aeval d f = 0) →
    (∃ f : Polynomial (v.adicCompletion ℚ), f.Monic ∧ (∀ i, f.coeff i ∈ v.adicCompletionIntegers ℚ) ∧ Polynomial.aeval d' f = 0) →
    ∃ a b : v.adicCompletion ℚ ⊗[ℚ] L, m = a * a - d * (b * b) := by
  intro L _ _ v hv m m' d d' hm hd im im' id id'
  obtain ⟨hH, hF⟩ := GlobalTheory.IntAdicHensel.henselianLocalRing_and_finite_residueField v
  letI : Algebra (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ ⊗[ℚ] L) :=
    ((algebraMap (v.adicCompletion ℚ) (v.adicCompletion ℚ ⊗[ℚ] L)).comp
      (v.adicCompletionIntegers ℚ).subtype).toAlgebra
  have key : ∀ x : v.adicCompletion ℚ ⊗[ℚ] L,
      (∃ f : Polynomial (v.adicCompletion ℚ), f.Monic ∧
        (∀ i, f.coeff i ∈ v.adicCompletionIntegers ℚ) ∧ Polynomial.aeval x f = 0) →
      IsIntegral (v.adicCompletionIntegers ℚ) x := by
    rintro x ⟨f, hf, hc, hx⟩
    obtain ⟨g, hg, -, hgm⟩ := Polynomial.lifts_and_natDegree_eq_and_monic
      (f := (v.adicCompletionIntegers ℚ).subtype)
      ((Polynomial.lifts_iff_coeff_lifts f).2 fun n => ⟨⟨_, hc n⟩, rfl⟩) hf
    refine ⟨g, hgm, ?_⟩
    rw [← hg, Polynomial.aeval_def, Polynomial.eval₂_map] at hx
    exact hx
  have h2 : (2 : ℤ) ∉ v.asIdeal := fun h =>
    hv ((PrincipalIdealRing.isMaximal_of_irreducible Int.prime_two.irreducible).eq_of_le
      v.isPrime.ne_top ((Ideal.span_singleton_le_iff_mem _).2 h)).symm
  have h2u : IsUnit (2 : v.adicCompletionIntegers ℚ) := by
    rw [adicCompletionIntegers.isUnit_iff_valued_eq_one]
    have h := valuedAdicCompletion_eq_valuation' v (2 : ℚ)
    have h' : v.valuation ℚ (2 : ℚ) = 1 := by
      have := (valuation_eq_one_iff_notMem v (K := ℚ) (r := (2 : ℤ))).2 h2
      simpa using this
    rw [h'] at h
    rw [← h]
    congr 1
    exact (map_ofNat (algebraMap ℚ (v.adicCompletion ℚ)) 2).symm
  exact exists_eq_of_isIntegral (v.adicCompletionIntegers ℚ) h2u hm hd
    (key _ im) (key _ im') (key _ id) (key _ id')

end GlobalTheory.OddLocalNorm
