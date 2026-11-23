import Mathlib
import GroundTheory.ArithmeticGeometry.SchemeCohomology.WeilDivisor
set_option maxSynthPendingDepth 1

namespace GroundTheory.Arith.SchemeCoh

open CategoryTheory AlgebraicGeometry IsDedekindDomain TopologicalSpace Topology

universe u

class IsLocallyFactorial (X : Scheme.{u}) : Prop where
  ufm_stalk : ∀ x : X, UniqueFactorizationMonoid (X.presheaf.stalk x)

variable {X : Scheme.{u}}

instance (priority := 100) IsLocallyFactorial.isNormalScheme [IsIntegral X]
    [IsLocallyFactorial X] : IsNormalScheme X where
  isDomain_stalk _ := inferInstance
  isIntegrallyClosed_stalk x := by
    have := IsLocallyFactorial.ufm_stalk (X := X) x
    infer_instance

namespace PrimeDivisor

variable [IsIntegral X] [IsLocallyNoetherian X] [IsNormalScheme X]

lemma ord_zero (x : PrimeDivisor X) : x.ord 0 = 0 := by
  simp [ord]

lemma ord_algebraMap_of_maximalIdeal_eq (x : PrimeDivisor X) {a : X.presheaf.stalk x.point}
    (ha : IsLocalRing.maximalIdeal (X.presheaf.stalk x.point) = Ideal.span {a}) :
    x.ord (algebraMap _ X.functionField a) = 1 := by
  have := x.isDedekindDomain_stalk
  have ha0 : a ≠ 0 := by
    rintro rfl
    exact x.maximalIdeal_ne_bot (by rw [ha, Ideal.span_singleton_eq_bot])
  simp only [ord, valuation]
  rw [HeightOneSpectrum.valuation_of_algebraMap,
    HeightOneSpectrum.intValuation_singleton _ ha0 ha]
  simp

omit [IsLocallyNoetherian X] [IsNormalScheme X] in

lemma heightOneSpectrum_eq (x : PrimeDivisor X)
    (w : HeightOneSpectrum (X.presheaf.stalk x.point)) : w = x.heightOneSpectrum := by
  have := x.dimensionLEOne_stalk
  have hmax : w.asIdeal.IsMaximal := Ring.DimensionLEOne.maximalOfPrime w.ne_bot w.isPrime
  ext1
  exact IsLocalRing.eq_maximalIdeal hmax

lemma ord_nonneg_iff (x : PrimeDivisor X) {f : X.functionField} (hf : f ≠ 0) :
    0 ≤ x.ord f ↔ f ∈ (algebraMap (X.presheaf.stalk x.point) X.functionField).range := by
  have := x.isDedekindDomain_stalk
  have hv0 : x.valuation f ≠ 0 := (Valuation.ne_zero_iff _).mpr hf
  have key : 0 ≤ x.ord f ↔ x.valuation f ≤ 1 := by
    simp only [ord, Left.nonneg_neg_iff]
    rw [WithZero.log_le_iff_le_exp hv0]
    simp
  rw [key]
  constructor
  · intro h
    apply HeightOneSpectrum.mem_integers_of_valuation_le_one
    intro w
    rw [x.heightOneSpectrum_eq w]
    exact h
  · rintro ⟨a, rfl⟩
    simp only [valuation]
    rw [HeightOneSpectrum.valuation_of_algebraMap]
    exact HeightOneSpectrum.intValuation_le_one _ _

end PrimeDivisor

section Algebra

variable {A : Type*} [CommRing A] [IsDomain A] (p : Ideal A) [p.IsPrime]

theorem exists_local_generator (S : Type*) [CommRing S] [IsDomain S] [Algebra A S]
    [IsLocalization.AtPrime S p] [UniqueFactorizationMonoid S]
    {q : Ideal A} [q.IsPrime] (hqp : q ≤ p) (hq : q.height = 1) :
    ∃ a ∈ q, (∀ b ∈ q, ∃ c : A, ∃ t : A, t ∉ p ∧ b * t = a * c) ∧
      ∀ q' : Ideal A, q'.IsPrime → q' ≤ p → q'.height = 1 → a ∈ q' → q' = q := by
  have hdisj : ∀ q' : Ideal A, q' ≤ p → Disjoint (p.primeCompl : Set A) (q' : Set A) :=
    fun q' h => Set.disjoint_left.mpr fun x hx hq' => hx (h hq')
  have hQ : (q.map (algebraMap A S)).IsPrime :=
    IsLocalization.isPrime_of_isPrime_disjoint p.primeCompl S q ‹_› (hdisj q hqp)
  have hQc : (q.map (algebraMap A S)).under A = q :=
    IsLocalization.under_map_of_isPrime_disjoint p.primeCompl S ‹q.IsPrime› (hdisj q hqp)
  have hQh : (q.map (algebraMap A S)).height = 1 := by
    rw [IsLocalization.height_map_of_disjoint p.primeCompl q (hdisj q hqp), hq]
  obtain ⟨π, hπ⟩ := (UniqueFactorizationMonoid.isPrincipal_of_height_eq_one hQh).principal
  obtain ⟨⟨a, s⟩, rfl⟩ := IsLocalization.mk'_surjective p.primeCompl π
  have hQa : q.map (algebraMap A S) = Ideal.span {algebraMap A S a} := by
    dsimp only at hπ
    rw [hπ]
    change Ideal.span {IsLocalization.mk' S a s} = _
    rw [IsLocalization.mk'_eq_mul_mk'_one,
      Ideal.span_singleton_mul_right_unit ((IsLocalization.AtPrime.isUnit_mk'_iff S p 1 s).mpr
        p.primeCompl.one_mem)]
  have hinj : Function.Injective (algebraMap A S) :=
    IsLocalization.injective S p.primeCompl_le_nonZeroDivisors
  refine ⟨a, ?_, ?_, ?_⟩
  · rw [← hQc, Ideal.under, Ideal.mem_comap, hQa]
    exact Ideal.mem_span_singleton_self _
  · intro b hb
    have hbQ : algebraMap A S b ∈ q.map (algebraMap A S) := Ideal.mem_map_of_mem _ hb
    rw [hQa, Ideal.mem_span_singleton'] at hbQ
    obtain ⟨z, hz⟩ := hbQ
    obtain ⟨⟨c, t⟩, rfl⟩ := IsLocalization.mk'_surjective p.primeCompl z
    refine ⟨c, t, t.2, hinj ?_⟩
    rw [map_mul, map_mul, ← hz, mul_comm (IsLocalization.mk' S c t), mul_assoc,
      IsLocalization.mk'_spec, mul_comm]
  · intro q' hq' hq'p hq'h haq'
    have hQ' : (q'.map (algebraMap A S)).IsPrime :=
      IsLocalization.isPrime_of_isPrime_disjoint p.primeCompl S q' hq' (hdisj q' hq'p)
    have hQ'h : (q'.map (algebraMap A S)).height = 1 := by
      rw [IsLocalization.height_map_of_disjoint p.primeCompl q' (hdisj q' hq'p), hq'h]
    have hle : q.map (algebraMap A S) ≤ q'.map (algebraMap A S) := by
      rw [hQa, Ideal.span_le, Set.singleton_subset_iff]
      exact Ideal.mem_map_of_mem _ haq'
    have : (q.map (algebraMap A S)).FiniteHeight := by
      simp [Ideal.finiteHeight_iff, hQh]
    have heq := Ideal.eq_of_le_of_height_le _ hle (by rw [hQh, hQ'h])
    rw [← hQc, heq, IsLocalization.under_map_of_isPrime_disjoint p.primeCompl S hq'
      (hdisj q' hq'p)]

end Algebra

section Hartogs

theorem mem_range_of_forall_prime (R : Type*) [CommRing R] [IsDomain R]
    [UniqueFactorizationMonoid R] {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]
    (f : K) (h : ∀ π : R, Prime π → ∃ b t : R, ¬ π ∣ t ∧ f * algebraMap R K t = algebraMap R K b) :
    f ∈ (algebraMap R K).range := by
  obtain ⟨a, c, hac, rfl⟩ := IsFractionRing.exists_reduced_fraction R f
  by_cases hc : IsUnit (c : R)
  · refine ⟨a * ↑hc.unit⁻¹, ?_⟩
    rw [eq_comm, IsLocalization.mk'_eq_iff_eq_mul, ← map_mul, mul_assoc, Units.inv_mul_eq_one.mpr
      hc.unit_spec.symm, mul_one]
  · obtain ⟨π, hπirr, hπc⟩ :=
      WfDvdMonoid.exists_irreducible_factor hc (nonZeroDivisors.ne_zero c.2)
    have hπ : Prime π := UniqueFactorizationMonoid.irreducible_iff_prime.mp hπirr
    obtain ⟨b, t, hπt, hft⟩ := h π hπ
    have key : a * t = b * c := by
      apply IsFractionRing.injective R K
      rw [map_mul, map_mul, ← hft, mul_comm (IsLocalization.mk' K a c), mul_assoc,
        IsLocalization.mk'_spec, mul_comm]
    have hπa : π ∣ a := by
      have : π ∣ a * t := key ▸ dvd_mul_of_dvd_right hπc b
      exact (hπ.dvd_or_dvd this).resolve_right hπt
    exact absurd (hac hπa hπc) hπ.not_isUnit

lemma height_span_prime {R : Type*} [CommRing R] [IsDomain R] [IsNoetherianRing R] {π : R}
    (hπ : Prime π) : (Ideal.span {π}).height = 1 := by
  have hprime : (Ideal.span {π}).IsPrime := (Ideal.span_singleton_prime hπ.ne_zero).mpr hπ
  apply le_antisymm
  · apply Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes (Ideal.span {π})
    rw [Ideal.minimalPrimes_eq_subsingleton_self]
    rfl
  · rw [Order.one_le_iff_ne_zero, Ne, Ideal.height_eq_zero_iff_eq_bot,
      Ideal.span_singleton_eq_bot]
    exact hπ.ne_zero

end Hartogs

section Affine

variable {U : X.Opens} (hU : IsAffineOpen U)

include hU in

lemma affine_fromSpec_mem (q : Spec Γ(X, U)) : hU.fromSpec q ∈ U := by
  rw [← SetLike.mem_coe, ← hU.range_fromSpec]
  exact ⟨q, rfl⟩

lemma affine_fromSpec_specializes_iff (q q' : Spec Γ(X, U)) :
    hU.fromSpec q ⤳ hU.fromSpec q' ↔ q.asIdeal ≤ q'.asIdeal := by
  rw [hU.fromSpec.isOpenEmbedding.isInducing.specializes_iff]
  exact (PrimeSpectrum.le_iff_specializes q q').symm

lemma affine_fromSpec_injective : Function.Injective hU.fromSpec :=
  hU.fromSpec.isOpenEmbedding.injective

lemma affine_height_eq_one (Z : PrimeDivisor X) (q : Spec Γ(X, U))
    (hq : hU.fromSpec q = Z.point) : q.asIdeal.height = 1 := by
  obtain ⟨z, hz⟩ := Z
  change hU.fromSpec q = z at hq
  subst hq
  have : q.asIdeal.IsPrime := PrimeSpectrum.isPrime q
  let _ := TopCat.Presheaf.algebra_section_stalk X.presheaf ⟨hU.fromSpec q, affine_fromSpec_mem hU q⟩
  have : IsLocalization.AtPrime (X.presheaf.stalk (hU.fromSpec q)) q.asIdeal :=
    hU.isLocalization_stalk' q (affine_fromSpec_mem hU q)
  have h := IsLocalization.AtPrime.ringKrullDim_eq_height q.asIdeal (X.presheaf.stalk (hU.fromSpec q))
  rw [hz] at h
  exact_mod_cast h.symm

variable [IsIntegral X] [IsLocallyNoetherian X] [IsNormalScheme X]

lemma affine_ord_eq_one (Z : PrimeDivisor X) (q : Spec Γ(X, U))
    (hq : hU.fromSpec q = Z.point) [Nonempty U] {a : Γ(X, U)} (ha : a ∈ q.asIdeal)
    (hgen : ∀ b ∈ q.asIdeal, ∃ c t : Γ(X, U), t ∉ q.asIdeal ∧ b * t = a * c) :
    Z.ord (X.germToFunctionField U a) = 1 := by
  obtain ⟨z, hz⟩ := Z
  change hU.fromSpec q = z at hq
  subst hq
  have : q.asIdeal.IsPrime := PrimeSpectrum.isPrime q
  let _ := TopCat.Presheaf.algebra_section_stalk X.presheaf ⟨hU.fromSpec q, affine_fromSpec_mem hU q⟩
  have : IsLocalization.AtPrime (X.presheaf.stalk (hU.fromSpec q)) q.asIdeal :=
    hU.isLocalization_stalk' q (affine_fromSpec_mem hU q)
  rw [← Scheme.algebraMap_germ_eq_germToFunctionField X (affine_fromSpec_mem hU q)]
  apply PrimeDivisor.ord_algebraMap_of_maximalIdeal_eq ⟨hU.fromSpec q, hz⟩
  change IsLocalRing.maximalIdeal (X.presheaf.stalk (hU.fromSpec q)) =
    Ideal.span {algebraMap Γ(X, U) (X.presheaf.stalk (hU.fromSpec q)) a}
  rw [← IsLocalization.AtPrime.map_eq_maximalIdeal q.asIdeal]
  apply le_antisymm
  · rw [Ideal.map_le_iff_le_comap]
    intro b hb
    obtain ⟨c, t, ht, hbt⟩ := hgen b hb
    rw [Ideal.mem_comap, Ideal.mem_span_singleton]
    have hu : IsUnit (algebraMap Γ(X, U) (X.presheaf.stalk (hU.fromSpec q)) t) :=
      (IsLocalization.AtPrime.isUnit_to_map_iff _ q.asIdeal t).mpr ht
    refine ⟨algebraMap _ _ c * ↑hu.unit⁻¹, ?_⟩
    have h2 := congrArg (algebraMap Γ(X, U) (X.presheaf.stalk (hU.fromSpec q))) hbt
    rw [map_mul, map_mul] at h2
    rw [← mul_assoc, ← h2, mul_assoc, IsUnit.mul_val_inv, mul_one]
  · rw [Ideal.span_le, Set.singleton_subset_iff]
    exact Ideal.mem_map_of_mem _ ha

lemma affine_ord_eq_zero (Z : PrimeDivisor X) (q : Spec Γ(X, U))
    (hq : hU.fromSpec q = Z.point) [Nonempty U] {a : Γ(X, U)} (ha : a ∉ q.asIdeal) :
    Z.ord (X.germToFunctionField U a) = 0 := by
  obtain ⟨z, hz⟩ := Z
  change hU.fromSpec q = z at hq
  subst hq
  have : q.asIdeal.IsPrime := PrimeSpectrum.isPrime q
  let _ := TopCat.Presheaf.algebra_section_stalk X.presheaf ⟨hU.fromSpec q, affine_fromSpec_mem hU q⟩
  have : IsLocalization.AtPrime (X.presheaf.stalk (hU.fromSpec q)) q.asIdeal :=
    hU.isLocalization_stalk' q (affine_fromSpec_mem hU q)
  rw [← Scheme.algebraMap_germ_eq_germToFunctionField X (affine_fromSpec_mem hU q)]
  exact PrimeDivisor.ord_algebraMap_of_isUnit ⟨hU.fromSpec q, hz⟩
    ((IsLocalization.AtPrime.isUnit_to_map_iff (X.presheaf.stalk (hU.fromSpec q)) q.asIdeal
      a).mpr ha)

end Affine

section Uniformizer

variable [IsIntegral X] [IsLocallyNoetherian X] [IsLocallyFactorial X]

theorem exists_local_uniformizer (x : X) (Y : PrimeDivisor X) (hYx : Y.point ⤳ x) :
    ∃ (U : X.Opens) (_ : Nonempty U) (a : Γ(X, U)), x ∈ U ∧
      Y.ord (X.germToFunctionField U a) = 1 ∧
      ∀ Z : PrimeDivisor X, Z.point ⤳ x → Z ≠ Y → Z.ord (X.germToFunctionField U a) = 0 := by
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  have hne : Nonempty U := ⟨⟨x, hxU⟩⟩
  set p := hU.primeIdealOf ⟨x, hxU⟩
  have hpx : hU.fromSpec p = x := hU.fromSpec_primeIdealOf ⟨x, hxU⟩
  have hmem : ∀ Z : PrimeDivisor X, Z.point ⤳ x → Z.point ∈ U :=
    fun Z hZ => hZ.mem_open U.isOpen hxU
  have hq : ∀ Z : PrimeDivisor X, ∀ hZ : Z.point ⤳ x,
      hU.fromSpec (hU.primeIdealOf ⟨Z.point, hmem Z hZ⟩) = Z.point :=
    fun Z hZ => hU.fromSpec_primeIdealOf ⟨Z.point, hmem Z hZ⟩
  have hle : ∀ Z : PrimeDivisor X, ∀ hZ : Z.point ⤳ x,
      (hU.primeIdealOf ⟨Z.point, hmem Z hZ⟩).asIdeal ≤ p.asIdeal := fun Z hZ =>
    (affine_fromSpec_specializes_iff hU _ p).mp (by rw [hq Z hZ, hpx]; exact hZ)
  have : p.asIdeal.IsPrime := PrimeSpectrum.isPrime p
  let _ := TopCat.Presheaf.algebra_section_stalk X.presheaf ⟨hU.fromSpec p, affine_fromSpec_mem hU p⟩
  have : IsLocalization.AtPrime (X.presheaf.stalk (hU.fromSpec p)) p.asIdeal :=
    hU.isLocalization_stalk' p (affine_fromSpec_mem hU p)
  have := IsLocallyFactorial.ufm_stalk (X := X) (hU.fromSpec p)
  obtain ⟨a, haq, hgen, huniq⟩ := exists_local_generator p.asIdeal
    (X.presheaf.stalk (hU.fromSpec p)) (hle Y hYx)
    (affine_height_eq_one hU Y _ (hq Y hYx))
  refine ⟨U, hne, a, hxU, ?_, ?_⟩
  · refine affine_ord_eq_one hU Y _ (hq Y hYx) haq fun b hb => ?_
    obtain ⟨c, t, ht, hbt⟩ := hgen b hb
    exact ⟨c, t, fun h => ht (hle Y hYx h), hbt⟩
  · intro Z hZx hZY
    refine affine_ord_eq_zero hU Z _ (hq Z hZx) fun haZ => hZY ?_
    have h := huniq _ inferInstance (hle Z hZx) (affine_height_eq_one hU Z _ (hq Z hZx)) haZ
    have h2 : hU.primeIdealOf ⟨Z.point, hmem Z hZx⟩ = hU.primeIdealOf ⟨Y.point, hmem Y hYx⟩ :=
      PrimeSpectrum.ext h
    apply PrimeDivisor.point_injective
    rw [← hq Z hZx, ← hq Y hYx, h2]

end Uniformizer

section LocallyPrincipal

variable [IsIntegral X] [IsNoetherian X] [IsLocallyFactorial X]

theorem WeilDivisor.exists_local_equation (D : WeilDivisor X) (x : X) :
    ∃ (V : X.Opens) (g : (X.functionField)ˣ), x ∈ V ∧
      ∀ Z : PrimeDivisor X, Z.point ∈ V → principalDivisor (Additive.ofMul g) Z = D Z := by
  classical
  have H : ∀ Y : PrimeDivisor X, ∃ u : (X.functionField)ˣ, Y.point ⤳ x →
      Y.ord (u : X.functionField) = 1 ∧
      ∀ Z : PrimeDivisor X, Z.point ⤳ x → Z ≠ Y → Z.ord (u : X.functionField) = 0 := by
    intro Y
    by_cases hY : Y.point ⤳ x
    · obtain ⟨U, hU, a, -, h1, h0⟩ := exists_local_uniformizer x Y hY
      have ha : X.germToFunctionField U a ≠ 0 := by
        intro h
        rw [h, PrimeDivisor.ord_zero] at h1
        exact zero_ne_one h1
      exact ⟨Units.mk0 _ ha, fun _ => ⟨h1, h0⟩⟩
    · exact ⟨1, fun h => absurd h hY⟩
  choose u hu using H
  set S : Finset (PrimeDivisor X) := D.support.filter (fun Y => Y.point ⤳ x)
  set g : (X.functionField)ˣ := ∏ Y ∈ S, u Y ^ D Y
  have hdiv : ∀ Z : PrimeDivisor X, Z.point ⤳ x → principalDivisor (Additive.ofMul g) Z = D Z := by
    intro Z hZ
    have hsum : principalDivisor (Additive.ofMul g) =
        ∑ Y ∈ S, D Y • principalDivisor (Additive.ofMul (u Y)) := by
      simp only [g, ofMul_prod, ofMul_zpow, map_sum, map_zsmul]
    rw [hsum, Finset.sum_apply']
    simp only [Finsupp.smul_apply, smul_eq_mul, principalDivisor_apply]
    by_cases hZS : Z ∈ S
    · rw [Finset.sum_eq_single Z]
      · rw [((hu Z) hZ).1, mul_one]
      · intro Y hY hYZ
        have hYx : Y.point ⤳ x := (Finset.mem_filter.mp hY).2
        rw [((hu Y) hYx).2 Z hZ (Ne.symm hYZ), mul_zero]
      · exact fun h => absurd hZS h
    · have hDZ : D Z = 0 := by
        by_contra hne
        exact hZS (Finset.mem_filter.mpr ⟨Finsupp.mem_support_iff.mpr hne, hZ⟩)
      rw [hDZ]
      refine Finset.sum_eq_zero fun Y hY => ?_
      have hYx : Y.point ⤳ x := (Finset.mem_filter.mp hY).2
      have hYZ : Z ≠ Y := fun h => hZS (h ▸ hY)
      rw [((hu Y) hYx).2 Z hZ hYZ, mul_zero]
  set T : Finset (PrimeDivisor X) :=
    (D.support ∪ (principalDivisor (Additive.ofMul g)).support).filter (fun Z => ¬ Z.point ⤳ x)
  have hT : IsClosed (⋃ Z ∈ T, closure {Z.point}) :=
    isClosed_biUnion_finset fun _ _ => isClosed_closure
  refine ⟨⟨(⋃ Z ∈ T, closure {Z.point})ᶜ, hT.isOpen_compl⟩, g, ?_, ?_⟩
  · show x ∈ (⋃ Z ∈ T, closure {Z.point})ᶜ
    simp only [Set.mem_compl_iff, Set.mem_iUnion, not_exists]
    intro Z hZ hxZ
    exact (Finset.mem_filter.mp hZ).2 (specializes_iff_mem_closure.mpr hxZ)
  · intro Z hZV
    by_cases hZx : Z.point ⤳ x
    · exact hdiv Z hZx
    · have hZT : Z ∉ T := by
        intro hZT
        have : Z.point ∈ (⋃ Z ∈ T, closure {Z.point}) :=
          Set.mem_biUnion hZT (subset_closure rfl)
        exact hZV this
      simp only [T, Finset.mem_filter, Finset.mem_union, Finsupp.mem_support_iff, not_and,
        not_not] at hZT
      by_cases h1 : D Z = 0
      · rw [h1]
        by_contra h2
        exact hZx (hZT (Or.inr h2))
      · exact absurd (hZT (Or.inl h1)) hZx

end LocallyPrincipal

section Regular

variable [IsIntegral X] [IsLocallyNoetherian X] [IsLocallyFactorial X]

theorem mem_range_stalk_of_ord_nonneg (x : X) (f : X.functionField)
    (h : ∀ Z : PrimeDivisor X, Z.point ⤳ x → 0 ≤ Z.ord f) :
    f ∈ (algebraMap (X.presheaf.stalk x) X.functionField).range := by
  by_cases hf0 : f = 0
  · exact ⟨0, by simp [hf0]⟩
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  have hne : Nonempty U := ⟨⟨x, hxU⟩⟩
  obtain ⟨p, rfl⟩ : ∃ p, hU.fromSpec p = x := ⟨_, hU.fromSpec_primeIdealOf ⟨x, hxU⟩⟩
  have : p.asIdeal.IsPrime := PrimeSpectrum.isPrime p
  let _ := TopCat.Presheaf.algebra_section_stalk X.presheaf ⟨hU.fromSpec p, affine_fromSpec_mem hU p⟩
  have : IsLocalization.AtPrime (X.presheaf.stalk (hU.fromSpec p)) p.asIdeal :=
    hU.isLocalization_stalk' p (affine_fromSpec_mem hU p)
  have := IsLocallyFactorial.ufm_stalk (X := X) (hU.fromSpec p)
  apply mem_range_of_forall_prime
  intro π hπ
  have hQ : (Ideal.span {π}).IsPrime := (Ideal.span_singleton_prime hπ.ne_zero).mpr hπ
  set q : Spec Γ(X, U) := ⟨(Ideal.span {π}).comap (algebraMap Γ(X, U) (X.presheaf.stalk (hU.fromSpec p))), Ideal.comap_isPrime _ _⟩
  have hqp : q.asIdeal ≤ p.asIdeal := by
    rw [← IsLocalization.AtPrime.under_maximalIdeal (X.presheaf.stalk (hU.fromSpec p)) p.asIdeal]
    apply Ideal.comap_mono
    rw [Ideal.span_le, Set.singleton_subset_iff]
    exact (IsLocalRing.mem_maximalIdeal π).mpr hπ.not_isUnit
  have hqh : q.asIdeal.height = 1 := by
    change (Ideal.under Γ(X, U) (Ideal.span {π})).height = 1
    rw [IsLocalization.height_under p.asIdeal.primeCompl, height_span_prime hπ]
  have hzx : hU.fromSpec q ⤳ hU.fromSpec p := (affine_fromSpec_specializes_iff hU q p).mpr hqp
  have : q.asIdeal.IsPrime := PrimeSpectrum.isPrime q
  let _ := TopCat.Presheaf.algebra_section_stalk X.presheaf ⟨hU.fromSpec q, affine_fromSpec_mem hU q⟩
  have hlocq : IsLocalization.AtPrime (X.presheaf.stalk (hU.fromSpec q)) q.asIdeal :=
    hU.isLocalization_stalk' q (affine_fromSpec_mem hU q)
  have hdim : ringKrullDim (X.presheaf.stalk (hU.fromSpec q)) = 1 := by
    rw [IsLocalization.AtPrime.ringKrullDim_eq_height q.asIdeal, hqh]
    rfl
  let Z : PrimeDivisor X := ⟨hU.fromSpec q, hdim⟩
  have hmem : f ∈ (algebraMap (X.presheaf.stalk (hU.fromSpec q)) X.functionField).range :=
    (Z.ord_nonneg_iff hf0).mp (h Z hzx)
  obtain ⟨w, hw⟩ := hmem
  obtain ⟨⟨b', t'⟩, rfl⟩ := IsLocalization.mk'_surjective q.asIdeal.primeCompl w
  have hcompat : ∀ (y : Spec Γ(X, U)) (a : Γ(X, U)),
      letI := TopCat.Presheaf.algebra_section_stalk X.presheaf ⟨hU.fromSpec y, affine_fromSpec_mem hU y⟩
      algebraMap (X.presheaf.stalk (hU.fromSpec y)) X.functionField
        (algebraMap Γ(X, U) (X.presheaf.stalk (hU.fromSpec y)) a) = X.germToFunctionField U a :=
    fun y a => Scheme.algebraMap_germ_eq_germToFunctionField X (affine_fromSpec_mem hU y) a
  have hft : f * X.germToFunctionField U t' = X.germToFunctionField U b' := by
    rw [← hw, ← hcompat q t', ← hcompat q b', ← map_mul]
    congr 1
    exact IsLocalization.mk'_spec _ _ _
  refine ⟨algebraMap Γ(X, U) (X.presheaf.stalk (hU.fromSpec p)) b',
    algebraMap Γ(X, U) (X.presheaf.stalk (hU.fromSpec p)) t', ?_, ?_⟩
  · intro hdvd
    apply t'.2
    change algebraMap Γ(X, U) (X.presheaf.stalk (hU.fromSpec p)) t' ∈ Ideal.span {π}
    exact Ideal.mem_span_singleton.mpr hdvd
  · rw [hcompat p t', hcompat p b', hft]

end Regular

section Regular

variable [IsIntegral X] [IsLocallyNoetherian X] [IsLocallyFactorial X]

theorem exists_section_of_ord_nonneg (V : X.Opens) [Nonempty V] (f : X.functionField)
    (h : ∀ Z : PrimeDivisor X, Z.point ∈ V → 0 ≤ Z.ord f) :
    ∃ s : Γ(X, V), X.germToFunctionField V s = f := by
  have hloc : ∀ x : V, ∃ (W : X.Opens) (hxW : x.1 ∈ W), W ≤ V ∧
      ∃ s : Γ(X, W), X.germToFunctionField W (h := ⟨⟨x.1, hxW⟩⟩) s = f := by
    intro x
    obtain ⟨w, hw⟩ := mem_range_stalk_of_ord_nonneg x.1 f
      (fun Z hZ => h Z (hZ.mem_open V.isOpen x.2))
    obtain ⟨W, hxW, g, hg⟩ := X.presheaf.exists_germ_eq w
    refine ⟨W ⊓ V, ⟨hxW, x.2⟩, inf_le_right, X.presheaf.map (homOfLE inf_le_left).op g, ?_⟩
    have : Nonempty W := ⟨⟨x.1, hxW⟩⟩
    rw [← hw, ← hg, Scheme.algebraMap_germ_eq_germToFunctionField]
    simp
  choose W hxW hWV s hs using hloc
  have hcompat : TopCat.Presheaf.IsCompatible X.sheaf.obj W s := by
    intro i j
    have hne : ((W i : Set X) ∩ W j).Nonempty :=
      nonempty_preirreducible_inter (W i).isOpen (W j).isOpen ⟨_, hxW i⟩ ⟨_, hxW j⟩
    obtain ⟨y, hy⟩ := hne
    have : Nonempty (W i ⊓ W j : X.Opens) := ⟨⟨y, hy⟩⟩
    have : Nonempty (W i) := ⟨⟨_, hxW i⟩⟩
    have : Nonempty (W j) := ⟨⟨_, hxW j⟩⟩
    apply Scheme.germToFunctionField_injective X (W i ⊓ W j)
    change X.germToFunctionField (W i ⊓ W j) (X.presheaf.map (homOfLE inf_le_left).op (s i)) =
      X.germToFunctionField (W i ⊓ W j) (X.presheaf.map (homOfLE inf_le_right).op (s j))
    simp [hs]
  obtain ⟨t, ht, -⟩ := X.sheaf.existsUnique_gluing' W V (fun i => homOfLE (hWV i))
    (fun x hx => Opens.mem_iSup.mpr ⟨⟨x, hx⟩, hxW _⟩) s hcompat
  refine ⟨t, ?_⟩
  obtain ⟨i⟩ := ‹Nonempty V›
  have : Nonempty (W i) := ⟨⟨_, hxW i⟩⟩
  rw [← hs i, ← ht i]
  change _ = X.germToFunctionField (W i) (X.presheaf.map (homOfLE (hWV i)).op t)
  exact (TopCat.Presheaf.germ_res_apply _ _ _ _ _).symm

end Regular

end GroundTheory.Arith.SchemeCoh
