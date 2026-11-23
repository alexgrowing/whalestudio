import Mathlib
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsDiscreteValuationRingLocalizationOfIsDedekindD
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.OrdFracEqValuationInvOfIsLocalization

open NumberField IsDedekindDomain IsLocalRing IsDiscreteValuationRing

namespace GlobalTheory

namespace OrderNorm

theorem length_quot_ringEquiv {T U : Type*} [CommRing T] [CommRing U] (e : T ≃+* U) (x : T) :
    Module.length T (T ⧸ Ideal.span {x}) = Module.length U (U ⧸ Ideal.span {e x}) := by
  let _ : Algebra T U := e.toRingHom.toAlgebra
  let f : T ≃ₐ[T] U := AlgEquiv.ofRingEquiv (f := e) (fun _ => rfl)
  have hI : Ideal.span {e x} = (Ideal.span {x}).map (f : T →+* U) := by
    rw [Ideal.map_span, Set.image_singleton]
    rfl
  rw [(Ideal.quotientEquivAlg (Ideal.span {x}) (Ideal.span {e x}) f hI).toLinearEquiv.length_eq]
  exact Module.length_eq_of_surjective e.surjective

theorem sum_maximal (A B : Type*) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [CommRing B] [Algebra A B] [Module.Free A B] [Module.Finite A B]
    [Fintype (MaximalSpectrum B)] {x : B} (hx : x ∈ nonZeroDivisors B) :
    ∑ n : MaximalSpectrum B, ((Module.length (Localization.AtPrime n.asIdeal)
        (Localization.AtPrime n.asIdeal ⧸
          Ideal.span {algebraMap B (Localization.AtPrime n.asIdeal) x})).toNat : ℝ) *
        Real.log (Nat.card (ResidueField (Localization.AtPrime n.asIdeal))) =
      ((addVal A (Algebra.norm A x)).toNat : ℝ) * Real.log (Nat.card (ResidueField A)) := by
  classical
  have hfin := (GlobalTheory.addVal_norm_ne_top_iff A x).mpr hx
  have hsum := GlobalTheory.addVal_norm_eq_sum_length A (fun n : MaximalSpectrum B => Localization.AtPrime n.asIdeal) hx
  have hloc : ∀ n : MaximalSpectrum B, IsLocalHom (algebraMap A (Localization.AtPrime n.asIdeal)) :=
    fun n => GlobalTheory.NormVal.isLocalHom_algebraMap A n.asIdeal _
  have hdeg : ∀ n : MaximalSpectrum B, n.asIdeal.inertiaDeg A =
      Module.finrank (ResidueField A) (ResidueField (Localization.AtPrime n.asIdeal)) :=
    fun n => GlobalTheory.NormVal.inertiaDeg_eq_finrank_residueField A n.asIdeal _
  have hcard : ∀ n : MaximalSpectrum B,
      Real.log (Nat.card (ResidueField (Localization.AtPrime n.asIdeal))) =
        (n.asIdeal.inertiaDeg A : ℝ) * Real.log (Nat.card (ResidueField A)) := by
    intro n
    have := GlobalTheory.NormVal.finite_residueField A n.asIdeal (Localization.AtPrime n.asIdeal)
    rw [hdeg n]
    rcases finite_or_infinite (ResidueField A) with hA | hA
    · rw [Module.natCard_eq_pow_finrank (K := ResidueField A), Nat.cast_pow, Real.log_pow]
    · have : Infinite (ResidueField (Localization.AtPrime n.asIdeal)) :=
        Infinite.of_injective _ (algebraMap (ResidueField A) _).injective
      simp [Nat.card_eq_zero_of_infinite]
  rw [hsum] at hfin ⊢
  rw [ENat.toNat_sum (ENat.sum_ne_top.mp hfin)]
  simp only [ENat.toNat_mul, ENat.toNat_natCast, Nat.cast_sum, Nat.cast_mul, Finset.sum_mul, hcard]
  refine Finset.sum_congr rfl fun n _ => ?_
  ring

theorem log_adicAbv (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))
    (A : Type*) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra (𝓞 F) A]
    [IsLocalization.AtPrime A v.asIdeal] [Algebra A F] [IsScalarTower (𝓞 F) A F]
    [IsFractionRing A F] {a : A} (ha : a ≠ 0) :
    ((addVal A a).toNat : ℝ) * Real.log (Nat.card (ResidueField A)) =
      -Real.log (NumberField.HeightOneSpectrum.adicAbv F v (algebraMap A F a)) := by
  have : v.asIdeal.IsMaximal := v.isMaximal
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible A
  obtain ⟨⟨r, s⟩, rfl⟩ := IsLocalization.mk'_surjective v.asIdeal.primeCompl a
  have hspec : IsLocalization.mk' A r s * algebraMap (𝓞 F) A s = algebraMap (𝓞 F) A r :=
    IsLocalization.mk'_spec A r s
  have hsu : IsUnit (algebraMap (𝓞 F) A s) := IsLocalization.map_units A s
  have hra : algebraMap (𝓞 F) A r ≠ 0 := by
    rw [← hspec]
    exact mul_ne_zero ha hsu.ne_zero
  have hr0 : r ≠ 0 := by
    rintro rfl
    exact hra (map_zero _)
  have hval : addVal A (IsLocalization.mk' A r s) = addVal A (algebraMap (𝓞 F) A r) := by
    rw [← hspec, addVal_mul, addVal_eq_zero_iff.mpr hsu, add_zero]
  obtain ⟨n, hn⟩ : ∃ n : ℕ, addVal A (algebraMap (𝓞 F) A r) = n :=
    ENat.ne_top_iff_exists.mp (fun h => hra (addVal_eq_top_iff.mp h)) |>.imp fun _ h => h.symm
  have hmem : ∀ k : ℕ, r ∈ v.asIdeal ^ k ↔ k ≤ n := by
    intro k
    rw [← IsLocalization.AtPrime.under_maximalIdeal_pow v.asIdeal A k, Ideal.under_def,
      Ideal.mem_comap, (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).mp hϖ,
      Ideal.span_singleton_pow, Ideal.mem_span_singleton, ← addVal_le_iff_dvd, addVal_pow,
      addVal_uniformizer hϖ, hn]
    simp
  have hne : v.intValuation r ≠ 0 := v.intValuation_ne_zero r hr0
  have hint : v.intValuation r = WithZero.exp (-(n : ℤ)) := by
    have h1 := (v.intValuation_le_pow_iff_mem r n).mpr ((hmem n).mpr le_rfl)
    have h2 : ¬ v.intValuation r ≤ WithZero.exp (-((n + 1 : ℕ) : ℤ)) := by
      rw [v.intValuation_le_pow_iff_mem r (n + 1), hmem]
      omega
    rw [← WithZero.exp_log hne] at h1 h2 ⊢
    rw [WithZero.exp_le_exp] at h1 h2
    congr 1
    push_cast at h2
    omega
  have hF : algebraMap A F (IsLocalization.mk' A r s) * algebraMap (𝓞 F) F s =
      algebraMap (𝓞 F) F r := by
    rw [IsScalarTower.algebraMap_apply (𝓞 F) A F s, IsScalarTower.algebraMap_apply (𝓞 F) A F r,
      ← map_mul, hspec]
  have hvF : v.valuation F (algebraMap A F (IsLocalization.mk' A r s)) =
      WithZero.exp (-(n : ℤ)) := by
    have := congrArg (v.valuation F) hF
    rw [map_mul, HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.valuation_of_algebraMap,
      (v.intValuation_eq_one_iff_mem_primeCompl (s : 𝓞 F)).mpr s.2, mul_one] at this
    rw [this, hint]
  have hcard : Nat.card (ResidueField A) = Ideal.absNorm v.asIdeal := by
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
    exact Nat.card_congr (IsLocalization.AtPrime.equivQuotMaximalIdeal v.asIdeal A).toEquiv.symm
  rw [NumberField.HeightOneSpectrum.adicAbv_def, hvF,
    WithZeroMulInt.toNNReal_neg_apply _ WithZero.exp_ne_zero, hval, hn, hcard]
  have hz : ∀ h : WithZero.exp (-(n : ℤ)) ≠ 0, Multiplicative.toAdd (WithZero.unzero h) = -(n : ℤ) :=
    fun _ => rfl
  rw [hz]
  simp

theorem finsum_eq_sum {O R : Type*} [CommRing O] [CommRing R] [Algebra O R] (p : Ideal O)
    [p.IsPrime] (A B : Type*) [CommRing A] [Algebra O A] [IsLocalization.AtPrime A p]
    [IsLocalRing A] [CommRing B] [Algebra R B]
    [IsLocalization (Algebra.algebraMapSubmonoid R p.primeCompl) B] [Algebra A B] [Algebra O B]
    [IsScalarTower O R B] [IsScalarTower O A B] [Module.Finite A B]
    [Fintype (MaximalSpectrum B)] (f : PrimeSpectrum R → ℝ) :
    ∑ᶠ (m : PrimeSpectrum R) (_ : m.asIdeal.comap (algebraMap O R) = p), f m =
      ∑ n : MaximalSpectrum B, f (PrimeSpectrum.comap (algebraMap R B) n.toPrimeSpectrum) := by
  classical
  let g : MaximalSpectrum B → PrimeSpectrum R :=
    fun n => PrimeSpectrum.comap (algebraMap R B) n.toPrimeSpectrum
  have hover : ∀ J : Ideal B, (J.comap (algebraMap R B)).comap (algebraMap O R) =
      (J.comap (algebraMap A B)).comap (algebraMap O A) := by
    intro J
    rw [Ideal.comap_comap, Ideal.comap_comap, ← IsScalarTower.algebraMap_eq O R B,
      ← IsScalarTower.algebraMap_eq O A B]
  have hinj : Function.Injective g := by
    intro n₁ n₂ h
    have h' : n₁.asIdeal.under R = n₂.asIdeal.under R := congrArg PrimeSpectrum.asIdeal h
    ext1
    rw [← IsLocalization.map_under (Algebra.algebraMapSubmonoid R p.primeCompl) B n₁.asIdeal,
      ← IsLocalization.map_under (Algebra.algebraMapSubmonoid R p.primeCompl) B n₂.asIdeal, h']
  have hrange : Set.range g = {m : PrimeSpectrum R | m.asIdeal.comap (algebraMap O R) = p} := by
    ext m
    constructor
    · rintro ⟨n, rfl⟩
      have hl := GlobalTheory.NormVal.liesOver_maximalIdeal A n.asIdeal
      have hu : n.asIdeal.comap (algebraMap A B) = IsLocalRing.maximalIdeal A := hl.over.symm
      show (n.asIdeal.comap (algebraMap R B)).comap (algebraMap O R) = p
      rw [hover, hu]
      exact IsLocalization.AtPrime.under_maximalIdeal A p
    · intro hm
      have hm : m.asIdeal.comap (algebraMap O R) = p := hm
      have hdisj : Disjoint ((Algebra.algebraMapSubmonoid R p.primeCompl : Submonoid R) : Set R)
          m.asIdeal := by
        rw [Set.disjoint_left]
        rintro _ ⟨s, hs, rfl⟩ hsm
        apply hs
        rw [← hm]
        exact hsm
      have hJp : (m.asIdeal.map (algebraMap R B)).IsPrime :=
        IsLocalization.isPrime_of_isPrime_disjoint _ B _ m.isPrime hdisj
      have hJc : (m.asIdeal.map (algebraMap R B)).comap (algebraMap R B) = m.asIdeal :=
        IsLocalization.under_map_of_isPrime_disjoint _ B m.isPrime hdisj
      have hJA : (m.asIdeal.map (algebraMap R B)).comap (algebraMap A B) =
          IsLocalRing.maximalIdeal A := by
        have hJO : ((m.asIdeal.map (algebraMap R B)).comap (algebraMap A B)).comap
            (algebraMap O A) = p := by
          rw [← hover, hJc, hm]
        have hJO' : Ideal.under O ((m.asIdeal.map (algebraMap R B)).comap (algebraMap A B)) = p :=
          hJO
        rw [← IsLocalization.map_under p.primeCompl A
          ((m.asIdeal.map (algebraMap R B)).comap (algebraMap A B)), hJO']
        exact IsLocalization.AtPrime.map_eq_maximalIdeal p A
      have hJm : (m.asIdeal.map (algebraMap R B)).IsMaximal :=
        Ideal.isMaximal_of_isIntegral_of_isMaximal_comap (R := A) _
          (hJA ▸ IsLocalRing.maximalIdeal.isMaximal A)
      refine ⟨⟨_, hJm⟩, ?_⟩
      ext1
      exact hJc
  calc ∑ᶠ (m : PrimeSpectrum R) (_ : m.asIdeal.comap (algebraMap O R) = p), f m
      = ∑ᶠ m ∈ Set.range g, f m := by rw [hrange]; rfl
    _ = ∑ᶠ n, f (g n) := finsum_mem_range hinj
    _ = ∑ n, f (g n) := finsum_eq_sum_of_fintype _

theorem local_term {R : Type*} [CommRing R] (M : Submonoid R) (B : Type*) [CommRing B]
    [Algebra R B] [IsLocalization M B] (n : Ideal B) [n.IsPrime] (T : Type*) [CommRing T]
    [IsLocalRing T] [Algebra R T] [IsLocalization.AtPrime T (n.comap (algebraMap R B))] (t : R) :
    Module.length T (T ⧸ Ideal.span {algebraMap R T t}) =
      Module.length (Localization.AtPrime n) (Localization.AtPrime n ⧸
        Ideal.span {algebraMap B (Localization.AtPrime n) (algebraMap R B t)}) ∧
    Nat.card (ResidueField T) = Nat.card (ResidueField (Localization.AtPrime n)) := by
  have := IsLocalization.isLocalization_isLocalization_atPrime_isLocalization M
    (Localization.AtPrime n) n
  let e : T ≃ₐ[R] Localization.AtPrime n :=
    IsLocalization.algEquiv (n.comap (algebraMap R B)).primeCompl T (Localization.AtPrime n)
  have he : e.toRingEquiv (algebraMap R T t) =
      algebraMap B (Localization.AtPrime n) (algebraMap R B t) := by
    change e (algebraMap R T t) = _
    rw [AlgEquiv.commutes, IsScalarTower.algebraMap_apply R B (Localization.AtPrime n)]
  refine ⟨?_, ?_⟩
  · have h := length_quot_ringEquiv e.toRingEquiv (algebraMap R T t)
    rw [he] at h
    exact h
  · exact Nat.card_congr (IsLocalRing.ResidueField.mapEquiv e.toRingEquiv).toEquiv

end OrderNorm

open OrderNorm in

theorem finsum_length_mul_log_card_eq_neg_log_adicAbv_norm (F : Type) [Field F] [NumberField F]
    (R K : Type) [CommRing R] [IsDomain R] [Field K] [Algebra (𝓞 F) R] [Module.Finite (𝓞 F) R]
    [Algebra R K] [IsFractionRing R K] [Algebra F K] [IsScalarTower (𝓞 F) R K]
    (S : PrimeSpectrum R → Type) [∀ m, CommRing (S m)] [∀ m, IsLocalRing (S m)]
    [∀ m, Algebra R (S m)] [∀ m : PrimeSpectrum R, IsLocalization.AtPrime (S m) m.asIdeal]
    (v : HeightOneSpectrum (𝓞 F)) (t : R) (ht : t ≠ 0) :
    ∑ᶠ (m : PrimeSpectrum R) (_ : m.asIdeal.comap (algebraMap (𝓞 F) R) = v.asIdeal),
      ((Module.length (S m) (S m ⧸ Ideal.span {algebraMap R (S m) t})).toNat : ℝ) *
        Real.log (Nat.card (IsLocalRing.ResidueField (S m))) =
      -Real.log (NumberField.HeightOneSpectrum.adicAbv F v
        (Algebra.norm F (algebraMap R K t))) := by
  classical
  have hvM : v.asIdeal.IsMaximal := v.isMaximal
  have hOK : Function.Injective (algebraMap (𝓞 F) K) := by
    rw [IsScalarTower.algebraMap_eq (𝓞 F) F K]
    exact (algebraMap F K).injective.comp (IsFractionRing.injective (𝓞 F) F)
  have hOR : Function.Injective (algebraMap (𝓞 F) R) := by
    intro a b h
    apply hOK
    rw [IsScalarTower.algebraMap_apply (𝓞 F) R K a, IsScalarTower.algebraMap_apply (𝓞 F) R K b, h]
  have hle : Algebra.algebraMapSubmonoid R v.asIdeal.primeCompl ≤ nonZeroDivisors R := by
    rintro _ ⟨s, hs, rfl⟩
    refine mem_nonZeroDivisors_of_ne_zero fun h => hs ?_
    rw [(map_eq_zero_iff _ hOR).mp h]
    exact zero_mem _
  have hleO : v.asIdeal.primeCompl ≤ nonZeroDivisors (𝓞 F) :=
    v.asIdeal.primeCompl_le_nonZeroDivisors
  have : IsDomain (Localization.AtPrime v.asIdeal) := IsLocalization.isDomain_localization hleO
  have : IsDiscreteValuationRing (Localization.AtPrime v.asIdeal) :=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain (𝓞 F) v.ne_bot _
  let _ : Algebra (Localization.AtPrime v.asIdeal) F := IsLocalization.localizationAlgebraOfSubmonoidLe _ F
    v.asIdeal.primeCompl (nonZeroDivisors (𝓞 F)) hleO
  have : IsScalarTower (𝓞 F) (Localization.AtPrime v.asIdeal) F :=
    IsLocalization.localization_isScalarTower_of_submonoid_le _ F _ _ hleO
  have : IsFractionRing (Localization.AtPrime v.asIdeal) F :=
    IsFractionRing.isFractionRing_of_isLocalization v.asIdeal.primeCompl _ F hleO
  have : IsDomain (Localization (Algebra.algebraMapSubmonoid R v.asIdeal.primeCompl)) := IsLocalization.isDomain_localization hle
  have hAB : Function.Injective (algebraMap (Localization.AtPrime v.asIdeal) (Localization (Algebra.algebraMapSubmonoid R v.asIdeal.primeCompl))) :=
    localizationAlgebra_injective (M := v.asIdeal.primeCompl) (S := R) (Rₘ := (Localization.AtPrime v.asIdeal))
      (Sₘ := (Localization (Algebra.algebraMapSubmonoid R v.asIdeal.primeCompl))) hOR
  have : Module.IsTorsionFree (Localization.AtPrime v.asIdeal) (Localization (Algebra.algebraMapSubmonoid R v.asIdeal.primeCompl)) :=
    Module.isTorsionFree_iff_algebraMap_injective.mpr hAB
  have : Module.Free (Localization.AtPrime v.asIdeal) (Localization (Algebra.algebraMapSubmonoid R v.asIdeal.primeCompl)) := Module.free_of_finite_type_torsion_free'
  have : Finite (MaximalSpectrum (Localization (Algebra.algebraMapSubmonoid R v.asIdeal.primeCompl))) := GlobalTheory.NormVal.finite_maximalSpectrum (Localization.AtPrime v.asIdeal) (S := (Localization (Algebra.algebraMapSubmonoid R v.asIdeal.primeCompl)))
  let _ : Fintype (MaximalSpectrum (Localization (Algebra.algebraMapSubmonoid R v.asIdeal.primeCompl))) := Fintype.ofFinite _
  let _ : Algebra (Localization (Algebra.algebraMapSubmonoid R v.asIdeal.primeCompl)) K := IsLocalization.localizationAlgebraOfSubmonoidLe _ K
    (Algebra.algebraMapSubmonoid R v.asIdeal.primeCompl) (nonZeroDivisors R) hle
  have : IsScalarTower R (Localization (Algebra.algebraMapSubmonoid R v.asIdeal.primeCompl)) K :=
    IsLocalization.localization_isScalarTower_of_submonoid_le _ K _ _ hle
  have : IsFractionRing (Localization (Algebra.algebraMapSubmonoid R v.asIdeal.primeCompl)) K :=
    IsFractionRing.isFractionRing_of_isLocalization _ _ K hle
  let _ : Algebra (Localization.AtPrime v.asIdeal) K := ((algebraMap F K).comp (algebraMap (Localization.AtPrime v.asIdeal) F)).toAlgebra
  have : IsScalarTower (Localization.AtPrime v.asIdeal) F K := IsScalarTower.of_algebraMap_eq' rfl
  have hO_AK : (algebraMap (Localization.AtPrime v.asIdeal) K).comp (algebraMap (𝓞 F) (Localization.AtPrime v.asIdeal)) = algebraMap (𝓞 F) K := by
    rw [IsScalarTower.algebraMap_eq (𝓞 F) F K, IsScalarTower.algebraMap_eq (𝓞 F) (Localization.AtPrime v.asIdeal) F]
    rfl
  have : IsScalarTower (Localization.AtPrime v.asIdeal) (Localization (Algebra.algebraMapSubmonoid R v.asIdeal.primeCompl)) K := by
    refine IsScalarTower.of_algebraMap_eq' (IsLocalization.ringHom_ext v.asIdeal.primeCompl ?_)
    rw [hO_AK, RingHom.comp_assoc, ← IsScalarTower.algebraMap_eq (𝓞 F) (Localization.AtPrime v.asIdeal) (Localization (Algebra.algebraMapSubmonoid R v.asIdeal.primeCompl)),
      IsScalarTower.algebraMap_eq (𝓞 F) R (Localization (Algebra.algebraMapSubmonoid R v.asIdeal.primeCompl)), ← RingHom.comp_assoc,
      ← IsScalarTower.algebraMap_eq R (Localization (Algebra.algebraMapSubmonoid R v.asIdeal.primeCompl)) K, ← IsScalarTower.algebraMap_eq (𝓞 F) R K]
  have : IsLocalization (Algebra.algebraMapSubmonoid (Localization (Algebra.algebraMapSubmonoid R v.asIdeal.primeCompl)) (nonZeroDivisors (Localization.AtPrime v.asIdeal))) K := by
    rw [isLocalization_iff]
    refine ⟨?_, fun z => ?_, ?_⟩
    · intro y
      obtain ⟨a, ha, hy⟩ := Submonoid.mem_map.mp y.2
      rw [isUnit_iff_ne_zero, ← hy, ← IsScalarTower.algebraMap_apply (Localization.AtPrime v.asIdeal) (Localization (Algebra.algebraMapSubmonoid R v.asIdeal.primeCompl)) K,
        IsScalarTower.algebraMap_apply (Localization.AtPrime v.asIdeal) F K]
      exact (map_ne_zero _).mpr ((map_ne_zero_iff _ (IsFractionRing.injective (Localization.AtPrime v.asIdeal) F)).mpr
        (nonZeroDivisors.ne_zero ha))
    · obtain ⟨b, c, hc, rfl⟩ := IsFractionRing.div_surjective (A := (Localization (Algebra.algebraMapSubmonoid R v.asIdeal.primeCompl))) z
      have hc0 : c ≠ 0 := nonZeroDivisors.ne_zero hc
      have hne := Ideal.comap_ne_bot_of_integral_mem (R := (Localization.AtPrime v.asIdeal)) hc0
        (Ideal.mem_span_singleton_self c) (Algebra.IsIntegral.isIntegral c)
      obtain ⟨a, ha, ha0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
      obtain ⟨d, hd⟩ := Ideal.mem_span_singleton'.mp (Ideal.mem_comap.mp ha)
      refine ⟨⟨b * d, ⟨algebraMap (Localization.AtPrime v.asIdeal) (Localization (Algebra.algebraMapSubmonoid R v.asIdeal.primeCompl)) a, a, mem_nonZeroDivisors_of_ne_zero ha0, rfl⟩⟩, ?_⟩
      have hc' : algebraMap (Localization (Algebra.algebraMapSubmonoid R v.asIdeal.primeCompl)) K c ≠ 0 :=
        (map_ne_zero_iff _ (IsFractionRing.injective (Localization (Algebra.algebraMapSubmonoid R v.asIdeal.primeCompl)) K)).mpr hc0
      simp only [Subtype.coe_mk]
      rw [← hd, map_mul, map_mul]
      field_simp
    · intro x y h
      refine ⟨1, ?_⟩
      simpa using IsFractionRing.injective (Localization (Algebra.algebraMapSubmonoid R v.asIdeal.primeCompl)) K h
  have hnorm : Algebra.norm F (algebraMap R K t) =
      algebraMap (Localization.AtPrime v.asIdeal) F (Algebra.norm (Localization.AtPrime v.asIdeal) (algebraMap R (Localization (Algebra.algebraMapSubmonoid R v.asIdeal.primeCompl)) t)) := by
    rw [IsScalarTower.algebraMap_apply R (Localization (Algebra.algebraMapSubmonoid R v.asIdeal.primeCompl)) K t]
    exact Algebra.norm_localization (Localization.AtPrime v.asIdeal) (nonZeroDivisors (Localization.AtPrime v.asIdeal)) (algebraMap R (Localization (Algebra.algebraMapSubmonoid R v.asIdeal.primeCompl)) t)
  have hx : algebraMap R (Localization (Algebra.algebraMapSubmonoid R v.asIdeal.primeCompl)) t ∈ nonZeroDivisors (Localization (Algebra.algebraMapSubmonoid R v.asIdeal.primeCompl)) :=
    mem_nonZeroDivisors_of_ne_zero ((map_ne_zero_iff _ (IsLocalization.injective _ hle)).mpr ht)
  have hN0 : Algebra.norm (Localization.AtPrime v.asIdeal) (algebraMap R (Localization (Algebra.algebraMapSubmonoid R v.asIdeal.primeCompl)) t) ≠ 0 := by
    intro h
    apply (GlobalTheory.addVal_norm_ne_top_iff (Localization.AtPrime v.asIdeal) _).mpr hx
    rw [h]
    exact IsDiscreteValuationRing.addVal_zero
  rw [hnorm, ← log_adicAbv F v (Localization.AtPrime v.asIdeal) hN0, ← sum_maximal (Localization.AtPrime v.asIdeal) (Localization (Algebra.algebraMapSubmonoid R v.asIdeal.primeCompl)) hx,
    finsum_eq_sum v.asIdeal (Localization.AtPrime v.asIdeal) (Localization (Algebra.algebraMapSubmonoid R v.asIdeal.primeCompl)) (fun m =>
      ((Module.length (S m) (S m ⧸ Ideal.span {algebraMap R (S m) t})).toNat : ℝ) *
        Real.log (Nat.card (IsLocalRing.ResidueField (S m))))]
  refine Finset.sum_congr rfl fun n _ => ?_
  have : IsLocalization.AtPrime (S (PrimeSpectrum.comap (algebraMap R (Localization (Algebra.algebraMapSubmonoid R v.asIdeal.primeCompl))) n.toPrimeSpectrum))
      (n.asIdeal.comap (algebraMap R (Localization (Algebra.algebraMapSubmonoid R v.asIdeal.primeCompl)))) :=
    inferInstanceAs (IsLocalization.AtPrime (S _)
      (PrimeSpectrum.comap (algebraMap R (Localization (Algebra.algebraMapSubmonoid R v.asIdeal.primeCompl))) n.toPrimeSpectrum).asIdeal)
  obtain ⟨h1, h2⟩ := local_term (Algebra.algebraMapSubmonoid R v.asIdeal.primeCompl) (Localization (Algebra.algebraMapSubmonoid R v.asIdeal.primeCompl)) n.asIdeal
    (S (PrimeSpectrum.comap (algebraMap R (Localization (Algebra.algebraMapSubmonoid R v.asIdeal.primeCompl))) n.toPrimeSpectrum)) t
  rw [h1, h2]

end GlobalTheory
