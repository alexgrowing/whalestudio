import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsTorsionFreeOfForallExists
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverIffIsProperAndExistsIsAmpleLB
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsLineBundleExtension
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.RingKrullDimQuotientEqOfMemMinimalPrimes

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite Limits Polynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.ProperCurve

section Algebra

variable {k K : Type} [Field k] [Field K]

theorem exists_mul_pow_mem_adjoin {R : Type} [CommRing R] [Algebra R K] {t y : K} (ht : t ≠ 0)
    (hy : y ∈ Algebra.adjoin R {t⁻¹}) : ∃ n : ℕ, ∀ m, n ≤ m → y * t ^ m ∈ Algebra.adjoin R {t} := by
  have hp : ∀ m : ℕ, t ^ m ∈ Algebra.adjoin R {t} := fun m =>
    pow_mem (Algebra.self_mem_adjoin_singleton R t) m
  induction hy using Algebra.adjoin_induction with
  | mem x hx =>
    obtain rfl : x = t⁻¹ := hx
    refine ⟨1, fun m hm => ?_⟩
    obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hm
    rw [pow_add, pow_one, ← mul_assoc, inv_mul_cancel₀ ht, one_mul]
    exact hp m
  | algebraMap r => exact ⟨0, fun m _ => mul_mem (Subalgebra.algebraMap_mem _ r) (hp m)⟩
  | add x y _ _ hx hy =>
    obtain ⟨a, ha⟩ := hx
    obtain ⟨b, hb⟩ := hy
    exact ⟨a + b, fun m hm => by
      rw [add_mul]; exact add_mem (ha m (by omega)) (hb m (by omega))⟩
  | mul x y _ _ hx hy =>
    obtain ⟨a, ha⟩ := hx
    obtain ⟨b, hb⟩ := hy
    refine ⟨a + b, fun m hm => ?_⟩
    obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hm
    have := mul_mem (ha a le_rfl) (hb (b + m) (by omega))
    convert this using 1
    ring

theorem exists_dvd_pow {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R] [Ring.KrullDimLE 1 R]
    {a c : R} (ha : a ∈ IsLocalRing.maximalIdeal R) (hc : c ≠ 0) : ∃ n, c ∣ a ^ n := by
  have : a ∈ (Ideal.span {c}).radical := by
    rw [Ideal.radical_eq_sInf, Ideal.mem_sInf]
    rintro p ⟨hp, hp'⟩
    have h0 : p ≠ ⊥ := fun h => hc (by
      have := hp (Ideal.mem_span_singleton_self c)
      rwa [h] at this)
    rw [IsLocalRing.eq_maximalIdeal (Ring.krullDimLE_one_iff_of_noZeroDivisors.1 ‹_› p h0 hp')]
    exact ha
  obtain ⟨n, hn⟩ := this
  exact ⟨n, Ideal.mem_span_singleton.1 hn⟩

theorem exists_pow_mem_maximalIdeal {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R]
    [Ring.KrullDimLE 1 R] [Algebra R K] [IsFractionRing R K] {a : R}
    (ha : a ∈ IsLocalRing.maximalIdeal R) (ha0 : a ≠ 0) {t : K} (ht : t ≠ 0)
    (H : ∀ V : ValuationSubring K, (∀ r, algebraMap R K r ∈ V) → V.valuation (algebraMap R K a) < 1 →
      V.valuation t < 1) :
    ∃ N : ℕ, ∀ n, N ≤ n → ∃ r ∈ IsLocalRing.maximalIdeal R, algebraMap R K r = t ^ n := by
  have H' : ∀ V : ValuationSubring K, (∀ r, algebraMap R K r ∈ V) → ∀ c : R, c ≠ 0 →
      V.valuation (algebraMap R K c) < 1 → V.valuation t < 1 := by
    intro V hV c hc h
    refine H V hV ?_
    obtain ⟨n, r, hr⟩ := exists_dvd_pow ha hc
    by_contra h'
    have h1 : V.valuation (algebraMap R K a) = 1 :=
      le_antisymm ((V.valuation_le_one_iff _).2 (hV a)) (not_lt.1 h')
    have h2 := congrArg (fun x => V.valuation (algebraMap R K x)) hr
    simp only [map_pow, map_mul, h1, one_pow] at h2
    exact absurd h2.symm (mul_lt_one_of_lt_of_le h ((V.valuation_le_one_iff _).2 (hV r))).ne
  have hint : IsIntegral R t := by
    by_contra hn
    have : IsIntegrallyClosedIn (integralClosure R K).toSubring K :=
      inferInstanceAs (IsIntegrallyClosedIn (integralClosure R K) K)
    obtain ⟨V, hV, htV⟩ := Subring.exists_le_valuationSubring_of_isIntegrallyClosedIn
      (R := (integralClosure R K).toSubring) (x := t) hn
    have hV' : ∀ r, algebraMap R K r ∈ V := fun r => hV (Subalgebra.algebraMap_mem _ r)
    obtain ⟨p, q, hq, rfl⟩ := IsFractionRing.div_surjective (A := R) t
    have hq1 : V.valuation (algebraMap R K q) = 1 :=
      le_antisymm ((V.valuation_le_one_iff _).2 (hV' q)) (not_lt.1 fun h =>
        htV ((V.valuation_le_one_iff _).1 (H' V hV' q (nonZeroDivisors.ne_zero hq) h).le))
    refine htV ((V.valuation_le_one_iff _).1 ?_)
    rw [map_div₀, hq1, div_one]
    exact (V.valuation_le_one_iff _).2 (hV' p)
  obtain ⟨d, hd, hd'⟩ := FractionalIdeal.isFractional_adjoin_integral (S := nonZeroDivisors R) t hint
  let A := (Algebra.adjoin R {t⁻¹}).toSubring
  have hc : d * a ≠ 0 := mul_ne_zero (nonZeroDivisors.ne_zero hd) ha0
  let c : A := ⟨algebraMap R K (d * a), Subalgebra.algebraMap_mem _ _⟩
  have htop : Ideal.span {c} = ⊤ := by
    by_contra hne
    obtain ⟨V, hV, hI⟩ := Ideal.image_subset_nonunits_valuationSubring _ hne
    have h1 := H' V (fun r => hV (Subalgebra.algebraMap_mem _ r)) _ hc
      (V.mem_nonunits_iff.1 (hI ⟨c, Ideal.mem_span_singleton_self c, rfl⟩))
    have h2 : V.valuation t⁻¹ ≤ 1 :=
      (V.valuation_le_one_iff _).2 (hV (Algebra.self_mem_adjoin_singleton R t⁻¹))
    have h3 := mul_lt_one_of_lt_of_le h1 h2
    rw [← map_mul, mul_inv_cancel₀ ht, map_one] at h3
    exact lt_irrefl _ h3
  obtain ⟨y, hy⟩ := (Ideal.span_singleton_eq_top.1 htop).exists_right_inv
  obtain ⟨N, hN⟩ := exists_mul_pow_mem_adjoin ht y.2
  refine ⟨N, fun n hn => ?_⟩
  obtain ⟨r, hr⟩ := hd' _ (hN n hn)
  refine ⟨a * r, Ideal.mul_mem_right _ _ ha, ?_⟩
  have hy' : algebraMap R K (d * a) * y = 1 := congrArg Subtype.val hy
  rw [map_mul, hr, Algebra.smul_def]
  rw [map_mul] at hy'
  linear_combination t ^ n * hy'

theorem valuation_div_lt_one {Γ : Type} [LinearOrderedCommGroupWithZero Γ] (v : Valuation K Γ) {c : K}
    (h : v c ≠ 1) : v (c / (1 + c ^ 2)) < 1 := by
  rw [map_div₀]
  rcases h.lt_or_gt with h | h
  · rw [v.map_one_add_of_lt (by rw [map_pow]; exact pow_lt_one₀ zero_le h two_ne_zero), div_one]
    exact h
  · have h0 : 0 < v c := zero_lt_one.trans h
    rw [v.map_add_eq_of_lt_right (by rw [map_pow, map_one]; exact one_lt_pow₀ h two_ne_zero),
      map_pow, div_lt_one₀ (pow_pos h0 2), sq]
    exact lt_mul_of_one_lt_left h0 h

variable [Algebra k[X] K]

theorem mem_of_polynomial_mem (V : ValuationSubring K) (hV : ∀ c : k, algebraMap k[X] K (C c) ∈ V)
    {q : k[X]} (hq : q.natDegree ≠ 0) (h : algebraMap k[X] K q ∈ V) : algebraMap k[X] K X ∈ V := by
  have hq0 : q ≠ 0 := by rintro rfl; simp at hq
  let φ : k →+* V := ((algebraMap k[X] K).comp C).codRestrict V hV
  have hm := monic_mul_leadingCoeff_inv hq0
  have e : aeval (algebraMap k[X] K X) ((q * C q.leadingCoeff⁻¹).map φ) =
      algebraMap k[X] K (q * C q.leadingCoeff⁻¹) := by
    rw [aeval_def, eval₂_map]
    exact (Polynomial.hom_eval₂ _ C (algebraMap k[X] K) X).symm.trans (by rw [eval₂_C_X])
  have hi : IsIntegral V (algebraMap k[X] K X) := by
    refine IsIntegral.of_aeval_monic (hm.map φ) ?_ ?_
    · rwa [hm.natDegree_map, natDegree_mul_leadingCoeff_inv _ hq0]
    · rw [e, map_mul]
      exact isIntegral_algebraMap (x := (⟨_, mul_mem h (hV _)⟩ : V))
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.1 hi
  exact hy ▸ y.2

theorem polynomial_mem (V : ValuationSubring K) (hV : ∀ c : k, algebraMap k[X] K (C c) ∈ V)
    (h : algebraMap k[X] K X ∈ V) (q : k[X]) : algebraMap k[X] K q ∈ V := by
  induction q using Polynomial.induction_on with
  | C a => exact hV a
  | add p q hp hq => rw [map_add]; exact add_mem hp hq
  | monomial n a ih => rw [pow_succ, ← mul_assoc, map_mul]; exact mul_mem ih h

theorem exists_polynomial [Algebra.IsAlgebraic k[X] K] {a : K} (ha : a ≠ 0) :
    ∃ p : k[X], p ≠ 0 ∧ ∀ q : k[X], p ∣ q → q.natDegree ≠ 0 → ∀ V : ValuationSubring K,
      (∀ c : k, algebraMap k[X] K (C c) ∈ V) → V.valuation a < 1 →
        V.valuation (algebraMap k[X] K q) ≠ 1 := by
  obtain ⟨b, hb, p, hp, e⟩ := (Algebra.IsAlgebraic.isAlgebraic (R := k[X]) a).exists_nonzero_eq_adjoin_mul
    (mem_nonZeroDivisors_of_ne_zero ha)
  refine ⟨p, hp, ?_⟩
  rintro _ ⟨r, rfl⟩ hq V hV h h1
  have hX := mem_of_polynomial_mem V hV hq ((V.valuation_le_one_iff _).1 h1.le)
  have hp := polynomial_mem V hV hX
  have hbV : b ∈ V := by
    clear e
    induction hb using Algebra.adjoin_induction with
    | mem x hx => obtain rfl : x = a := hx; exact (V.valuation_le_one_iff _).1 h.le
    | algebraMap r => exact hp r
    | add x y _ _ hx hy => exact add_mem hx hy
    | mul x y _ _ hx hy => exact mul_mem hx hy
  rw [map_mul, ← e, mul_assoc, map_mul] at h1
  exact (mul_lt_one_of_lt_of_le h ((V.valuation_le_one_iff _).2 (mul_mem hbV (hp r)))).ne h1

omit [Algebra k[X] K] in

theorem exists_polynomial_integral (A : Type) [CommRing A] [IsDomain A] [Algebra k A]
    [Algebra.FiniteType k A] (h : ringKrullDim A = 1) :
    ∃ g : k[X] →ₐ[k] A, Function.Injective g ∧ g.toRingHom.IsIntegral := by
  obtain ⟨s, g, hg, hint⟩ := exists_integral_inj_algHom_of_fg k A
  obtain rfl : s = 1 := by
    let := g.toRingHom.toAlgebra
    have : FaithfulSMul (MvPolynomial (Fin s) k) A :=
      (faithfulSMul_iff_algebraMap_injective _ _).mpr hg
    have : Algebra.IsIntegral (MvPolynomial (Fin s) k) A := ⟨hint⟩
    rw [ringKrullDim_eq_of_isIntegral (MvPolynomial (Fin s) k) A,
      MvPolynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field] at h
    simpa using h
  let e := (MvPolynomial.uniqueAlgEquiv k (Fin 1)).symm
  exact ⟨g.comp e.toAlgHom, hg.comp e.injective,
    RingHom.IsIntegral.trans (e : k[X] →+* _) _ (RingHom.isIntegral_of_surjective _ e.surjective) hint⟩

end Algebra

section Geometry

open GlobalTheory.ExtendLineBundle GlobalTheory.ProjSpace

variable {C : Scheme.{0}} [IsIntegral C]

local instance specOrder (X : Scheme.{0}) : PartialOrder X := specializationOrder X

theorem mem_localSubring_genericPoint (t : C.functionField) : t ∈ localSubring (genericPoint C) := by
  obtain ⟨U, hU, s, rfl⟩ := C.presheaf.exists_germ_eq t
  exact germ_mem hU hU s

omit [IsIntegral C] in

theorem krullDim_eq : Order.krullDim C = topologicalKrullDim C :=
  (Order.krullDim_eq_of_orderIso (irreducibleSetEquivPoints (α := C))).symm

theorem isClosed_singleton (hd : topologicalKrullDim C = 1) {x : C} (hx : x ≠ genericPoint C) :
    IsClosed ({x} : Set C) := by
  rcases Order.krullDim_le_one_iff.1 (krullDim_eq.trans hd).le x with h | h
  · rw [← closure_subset_iff_isClosed]
    intro y hy
    have : y ≤ x := specializes_iff_mem_closure.2 hy
    exact le_antisymm this (h this)
  · have : x ≤ genericPoint C := genericPoint_specializes x
    exact absurd (le_antisymm this (h this)) hx

theorem exists_ne_genericPoint (hd : topologicalKrullDim C = 1) : ∃ x : C, x ≠ genericPoint C := by
  obtain ⟨x, y, h⟩ := Order.krullDim_pos_iff.1 (zero_lt_one.trans_eq (krullDim_eq.trans hd).symm)
  exact ⟨x, fun e => h.not_ge (e ▸ (genericPoint_specializes y : y ≤ genericPoint C))⟩

theorem finite_of_isClosed [NoetherianSpace C] (hd : topologicalKrullDim C = 1) {Z : Set C}
    (hZ : IsClosed Z) (h : genericPoint C ∉ Z) : Z.Finite := by
  obtain ⟨S, hS, hc, hi, rfl⟩ := NoetherianSpace.exists_finite_set_isClosed_irreducible hZ
  refine hS.sUnion fun T hT => ?_
  have hg := (hi T hT).isGenericPoint_genericPoint (hc T hT)
  have : (hi T hT).genericPoint ≠ genericPoint C := fun e => h ⟨T, hT, e ▸ hg.mem⟩
  rw [← hg.def, (isClosed_singleton hd this).closure_eq]
  exact Set.finite_singleton _

theorem krullDimLE_stalk (hd : topologicalKrullDim C = 1) (x : C) :
    Ring.KrullDimLE 1 (C.presheaf.stalk x) := by
  refine krullDimLE_of_coheight_le ?_
  have := (Order.coheight_le_krullDim x).trans (krullDim_eq.trans hd).le
  exact_mod_cast this

theorem exists_mem_maximalIdeal {x : C} (hx : x ≠ genericPoint C) :
    ∃ a ∈ IsLocalRing.maximalIdeal (C.presheaf.stalk x), a ≠ 0 := by
  refine Submodule.exists_mem_ne_zero_of_ne_bot fun h => hx ?_
  have h0 := ringKrullDim_eq_zero_of_isField (IsLocalRing.isField_iff_maximalIdeal_eq.2 h)
  rw [ringKrullDim_stalk_eq_coheight] at h0
  have h1 : IsMax x := Order.coheight_eq_zero.1 (by exact_mod_cast h0)
  have : x ≤ genericPoint C := genericPoint_specializes x
  exact le_antisymm this (h1 this)

theorem ringKrullDim_eq_one (hd : topologicalKrullDim C = 1) {U : C.Opens} (hU : IsAffineOpen U)
    {x : C} (hxU : x ∈ U) (hx : x ≠ genericPoint C) : ringKrullDim Γ(C, U) = 1 := by
  refine le_antisymm ?_ ?_
  · rw [← PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim, ← hd]
    exact hU.fromSpec.isOpenEmbedding.isInducing.topologicalKrullDim_le
  · have hη := genericPoint_mem hxU
    have hlt : hU.primeIdealOf ⟨_, hη⟩ < hU.primeIdealOf ⟨x, hxU⟩ := by
      refine lt_of_le_of_ne ((PrimeSpectrum.le_iff_specializes _ _).2 ?_) fun e => hx ?_
      · refine hU.fromSpec.isOpenEmbedding.isInducing.specializes_iff.1 ?_
        rw [hU.fromSpec_primeIdealOf, hU.fromSpec_primeIdealOf]
        exact genericPoint_specializes x
      · have := congrArg hU.fromSpec e
        rw [hU.fromSpec_primeIdealOf, hU.fromSpec_primeIdealOf] at this
        exact this.symm
    exact Order.one_le_krullDim_iff.2 ⟨_, _, hlt⟩

theorem exists_function {k : Type} [Field k] (f : C ⟶ Sp k) [LocallyOfFiniteType f]
    [NoetherianSpace C] (hd : topologicalKrullDim C = 1) :
    ∃ τ : C.functionField, τ ≠ 0 ∧ (∃ x, τ⁻¹ ∉ localSubring x) ∧
      ∀ x, τ ∈ localSubring x ∨ τ⁻¹ ∈ localSubring x := by
  classical
  obtain ⟨x₀, hx₀⟩ := exists_ne_genericPoint hd
  obtain ⟨U, hU, hxU, -⟩ := exists_isAffineOpen_mem_and_subset (U := ⊤) (x := x₀) trivial
  have hη := genericPoint_mem hxU
  have : Nonempty U := ⟨⟨_, hxU⟩⟩
  let ρ : k →+* Γ(C, U) := ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appLE ⊤ U le_top).hom
  have hρ : ρ.FiniteType :=
    (f.finiteType_appLE (isAffineOpen_top _) hU le_top).comp
      (RingHom.FiniteType.of_surjective _
        (Scheme.ΓSpecIso (.of k)).symm.commRingCatIsoToRingEquiv.surjective)
  let := ρ.toAlgebra
  have : Algebra.FiniteType k Γ(C, U) := hρ
  obtain ⟨g, hg, hint⟩ := exists_polynomial_integral (k := k) Γ(C, U) (ringKrullDim_eq_one hd hU hxU hx₀)
  have := functionField_isFractionRing_of_isAffineOpen C U hU
  let := g.toRingHom.toAlgebra
  let : Algebra k[X] C.functionField :=
    ((algebraMap Γ(C, U) C.functionField).comp g.toRingHom).toAlgebra
  have : IsScalarTower k[X] Γ(C, U) C.functionField := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : FaithfulSMul k[X] Γ(C, U) := (faithfulSMul_iff_algebraMap_injective _ _).mpr hg
  have : Algebra.IsIntegral k[X] Γ(C, U) := ⟨hint⟩
  have : Algebra.IsAlgebraic Γ(C, U) C.functionField :=
    IsLocalization.isAlgebraic _ (nonZeroDivisors _)
  have : Algebra.IsAlgebraic k[X] C.functionField := Algebra.IsAlgebraic.trans _ Γ(C, U) _
  have hinj : Function.Injective (algebraMap k[X] C.functionField) :=
    (IsFractionRing.injective Γ(C, U) C.functionField).comp hg
  have hconst : ∀ (c : k) (x : C), algebraMap k[X] C.functionField (Polynomial.C c) ∈ localSubring x := by
    intro c x
    have e : algebraMap k[X] C.functionField (Polynomial.C c) =
        C.presheaf.germ ⊤ _ trivial (f.appTop ((Scheme.ΓSpecIso (.of k)).inv c)) := by
      change C.presheaf.germ U _ hη (g (algebraMap k k[X] c)) = _
      rw [g.commutes]
      exact C.presheaf.germ_res_apply (homOfLE le_top) _ hη _
    rw [e]
    exact germ_mem (U := ⊤) trivial _ _
  let S : Set C := insert x₀ (U : Set C)ᶜ
  have hSη : ∀ x : S, x.1 ≠ genericPoint C := by
    rintro ⟨x, rfl | hx⟩
    · exact hx₀
    · rintro rfl; exact hx hη
  have : Finite S := ((finite_of_isClosed hd U.isOpen.isClosed_compl fun h => h hη).insert x₀).to_subtype
  have := Fintype.ofFinite S
  choose a ha ha0 using fun x : S => exists_mem_maximalIdeal (hSη x)
  choose p hp0 hp using fun x : S => exists_polynomial (k := k)
    ((map_ne_zero_iff _ (IsFractionRing.injective _ C.functionField)).2 (ha0 x))
  let q : k[X] := X * ∏ x, p x
  have hq0 : q ≠ 0 := mul_ne_zero X_ne_zero (Finset.prod_ne_zero_iff.2 fun x _ => hp0 x)
  have hq : q.natDegree ≠ 0 := by
    rw [natDegree_X_mul (right_ne_zero_of_mul hq0)]; omega
  set c := algebraMap k[X] C.functionField q with hc
  have hc0 : c ≠ 0 := (map_ne_zero_iff _ hinj).2 hq0
  have hc1 : 1 + c ^ 2 ≠ 0 := by
    rw [hc, ← map_pow, ← map_one (algebraMap k[X] C.functionField), ← map_add, map_ne_zero_iff _ hinj]
    intro h
    simpa [q] using congrArg (eval 0) h
  have ht := div_ne_zero hc0 hc1
  choose N hN using fun x : S =>
    have := krullDimLE_stalk hd x.1
    exists_pow_mem_maximalIdeal (ha x) (ha0 x) ht fun V hV h => valuation_div_lt_one _
      (hp x q ((Finset.dvd_prod_of_mem p (Finset.mem_univ x)).mul_left X) hq V
        (fun c => by obtain ⟨r, hr⟩ := hconst c x; exact hr ▸ hV r) h)
  have hN' := fun x : S => hN x _ (Finset.le_sup (f := N) (Finset.mem_univ x))
  refine ⟨(c / (1 + c ^ 2)) ^ Finset.univ.sup N, pow_ne_zero _ ht, ⟨x₀, ?_⟩, fun x => ?_⟩
  · obtain ⟨r, hr, e⟩ := hN' ⟨x₀, Set.mem_insert _ _⟩
    rintro ⟨s, hs⟩
    refine hr (IsUnit.of_mul_eq_one s (IsFractionRing.injective _ C.functionField ?_))
    rw [map_mul, map_one, e, hs, mul_inv_cancel₀ (pow_ne_zero _ ht)]
  · by_cases hx : x ∈ U
    · obtain ⟨r, hr⟩ : c ∈ localSubring x := germ_mem hx hη (g q)
      have key : ∀ u v : C.presheaf.stalk x, IsUnit v →
          algebraMap _ C.functionField u / algebraMap _ C.functionField v ∈ localSubring x := by
        rintro u _ ⟨v, rfl⟩
        exact ⟨u * ↑v⁻¹, by rw [map_mul, map_units_inv, div_eq_mul_inv]⟩
      by_cases hu : IsUnit r
      · right
        rw [← inv_pow, inv_div]
        refine pow_mem ?_ _
        have := key (1 + r ^ 2) r hu
        rwa [map_add, map_one, map_pow, hr] at this
      · left
        refine pow_mem ?_ _
        have hu' : IsUnit (1 + r ^ 2) := by
          refine (IsLocalRing.isUnit_or_isUnit_of_add_one (a := 1 + r ^ 2) (b := -r ^ 2)
            (by ring)).resolve_right fun h => hu ?_
          exact (isUnit_pow_iff two_ne_zero).1 ((IsUnit.neg_iff _).1 h)
        simpa only [map_add, map_one, map_pow, hr] using key r (1 + r ^ 2) hu'
    · obtain ⟨r, -, e⟩ := hN' ⟨x, Set.mem_insert_of_mem _ hx⟩
      exact .inl ⟨r, e⟩

theorem exists_hom {k : Type} [Field k] (f : C ⟶ Sp k) {n : ℕ} (t : Fin (n + 1) → C.functionField)
    (ht : ∀ i, t i ≠ 0) (H : ∀ x, ∃ i, ∀ j, t j / t i ∈ localSubring x) :
    ∃ φ : C ⟶ PSpace k n, φ ≫ PSpace.str k n = f ∧
      ∀ i x, φ x ∈ chart k n i ↔ ∀ j, t j / t i ∈ localSubring x := by
  let U : Fin (n + 1) → C.Opens := fun i => ⟨{x | ∀ j, t j / t i ∈ localSubring x},
    isOpen_iff_mem_nhds.2 fun x hx => Filter.eventually_all.2 fun j => eventually_mem (hx j)⟩
  have hη : ∀ i, genericPoint C ∈ U i := fun i j => mem_localSubring_genericPoint _
  choose r hr using fun i j => exists_section (hη i) (t := t j / t i) fun x hx => hx j
  have hF : IsCoordFamily U r := by
    refine ⟨top_le_iff.1 fun x _ => Opens.mem_iSup.2 (H x), fun i => ?_, fun i j l => ?_,
      fun i j x hx l => ?_⟩
    · refine germ_injective_of_isIntegral C _ (hη i) ?_
      rw [hr, map_one, div_self (ht i)]
    · refine germ_injective_of_isIntegral C (U := U i ⊓ U j) _ ⟨hη i, hη j⟩ ?_
      have e : ∀ (V : C.Opens) (h : U i ⊓ U j ≤ V) (s : Γ(C, V)),
          C.presheaf.germ (U i ⊓ U j) _ ⟨hη i, hη j⟩ (resG C h s) =
            C.presheaf.germ V _ (h ⟨hη i, hη j⟩) s := fun V h s =>
        C.presheaf.germ_res_apply (homOfLE h) _ _ _
      rw [map_mul, e, e, e, hr, hr, hr]
      change (t j / t i) * (t l / t j) = t l / t i
      field_simp [ht i, ht j]
    · have h1 := (inv_germ_mem _ (hη i) hx).2
      rw [hr] at h1
      have h2 := mul_mem (C.basicOpen_le _ hx l) h1
      convert h2 using 1
      field_simp [ht i, ht j]
  exact ⟨hF.toHom f, hF.toHom_str f, fun i x => SetLike.ext_iff.1 (hF.toHom_preimage f i) x⟩

theorem locallyQuasiFinite_of_ne [NoetherianSpace C] (hd : topologicalKrullDim C = 1) {Y : Scheme.{0}}
    (φ : C ⟶ Y) [IsProper φ] {x₀ : C} (h : φ x₀ ≠ φ (genericPoint C)) : LocallyQuasiFinite φ := by
  refine .of_finite_preimage_singleton φ fun y => ?_
  by_cases hx : ∃ x, x ≠ genericPoint C ∧ φ x = y
  · obtain ⟨x, hx, rfl⟩ := hx
    have hc : IsClosed (φ ⁻¹' {φ x}) := by
      refine IsClosed.preimage φ.continuous ?_
      rw [← Set.image_singleton]
      exact φ.isClosedMap _ (isClosed_singleton hd hx)
    refine finite_of_isClosed hd hc fun hη => h ?_
    exact ((genericPoint_specializes x₀).mem_closed hc hη).trans hη.symm
  · refine (Set.finite_singleton (genericPoint C)).subset fun x hx' => ?_
    by_contra hne
    exact hx ⟨x, hne, hx'⟩

theorem isProjOver_of_isProper {k : Type} [Field k] (f : C ⟶ Sp k) [IsProper f]
    (hd : topologicalKrullDim C = 1) : IsProjOver f := by
  have : CompactSpace C := QuasiCompact.compactSpace_of_compactSpace f
  have := isNoetherian_of_locallyOfFiniteType_field f
  obtain ⟨τ, h0, ⟨x₀, hx₀⟩, H⟩ := exists_function f hd
  obtain ⟨φ, rfl, hφ⟩ := exists_hom f ![1, τ] (by simp [Fin.forall_fin_two, h0]) fun x => by
    rcases H x with h | h
    · exact ⟨0, by simpa [Fin.forall_fin_two, one_mem] using h⟩
    · exact ⟨1, by simpa [Fin.forall_fin_two, one_mem, h0] using h⟩
  have := (isProper_and_exists_isAmpleLB_of_isProjOver (isProjOver_str k 1)).1
  have : IsProper φ := .of_comp φ (PSpace.str k 1)
  have : LocallyQuasiFinite φ := locallyQuasiFinite_of_ne hd φ (x₀ := x₀) fun e => hx₀ (by
    simpa using (hφ 1 x₀).1 (e ▸ (hφ 1 _).2 fun j => mem_localSubring_genericPoint _) 0)
  have := IsFinite.of_isProper_of_locallyQuasiFinite φ
  exact isProjOver_comp_of_isFinite φ (isProjOver_str k 1)

end Geometry

end GlobalTheory.ProperCurve

namespace GlobalTheory.VB

theorem IsProperCurve.isProjCurve (k : Type) [Field k] (C : Scheme.{0}) [Algebra k Γ(C, ⊤)]
    [IsIntegral C] (h : IsProperCurve k C) : IsProjCurve k C :=
  have := h.isProper
  ⟨h.isIntegral, h.dim_eq, ProperCurve.isProjOver_of_isProper _ h.dim_eq⟩

end GlobalTheory.VB
