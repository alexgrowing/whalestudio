import Mathlib
import GroundTheory.FunctionField.PlaceAbove

namespace GroundTheory.FunctionField

open IsDedekindDomain IsLocalRing

open scoped WithZero

theorem valuation_eq_of_isEquiv {F : Type*} [Field F] {v₁ v₂ : Valuation F ℤᵐ⁰}
    (h : v₁.IsEquiv v₂) (h₁ : Function.Surjective v₁) (h₂ : Function.Surjective v₂) : v₁ = v₂ := by
  have disc : ∀ y : ℤᵐ⁰, y < 1 → y ≤ WithZero.exp (-1) := by
    intro y hy
    rcases eq_or_ne y 0 with rfl | hy0
    · exact zero_le
    · rw [← WithZero.exp_log hy0, ← WithZero.exp_zero, WithZero.exp_lt_exp] at hy
      rw [← WithZero.exp_log hy0, WithZero.exp_le_exp]
      omega
  have hlt : WithZero.exp (-1 : ℤ) < 1 := by
    rw [← WithZero.exp_zero, WithZero.exp_lt_exp]; omega
  obtain ⟨π, hπ⟩ := h₁ (WithZero.exp (-1))
  obtain ⟨π', hπ'⟩ := h₂ (WithZero.exp (-1))
  have hπ2 : v₂ π = WithZero.exp (-1) := by
    have h2lt : v₂ π < 1 := h.lt_one_iff_lt_one.1 (hπ ▸ hlt)
    have h1 : v₁ π' < 1 := h.lt_one_iff_lt_one.2 (hπ' ▸ hlt)
    have h3 : v₂ π' ≤ v₂ π := h.le_iff_le.1 (hπ ▸ disc _ h1)
    exact le_antisymm (disc _ h2lt) (hπ' ▸ h3)
  ext x
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  have hx1 : v₁ x = WithZero.exp (WithZero.log (v₁ x)) :=
    (WithZero.exp_log ((Valuation.ne_zero_iff _).2 hx)).symm
  have hy : v₁ (x * π ^ (WithZero.log (v₁ x))) = 1 := by
    rw [map_mul, map_zpow₀, hπ, hx1, WithZero.log_exp, ← WithZero.exp_zsmul, ← WithZero.exp_add]
    rw [← WithZero.exp_zero]
    congr 1
    simp
  have hy2 := h.eq_one_iff_eq_one.1 hy
  rw [map_mul, map_zpow₀, hπ2, ← WithZero.exp_zsmul] at hy2
  rw [hx1, eq_inv_of_mul_eq_one_left hy2, ← WithZero.exp_neg]
  congr 1
  simp

namespace Place

variable {k K K' : Type*} [Field k] [Field K] [Field K'] [Algebra k K] [Algebra k K']
  [Algebra K K'] [IsScalarTower k K K']

noncomputable abbrev algebraExt (v : Place k K) : Algebra v.ring K' :=
  ((algebraMap K K').comp (algebraMap v.ring K)).toAlgebra

attribute [local instance low] algebraExt

omit [Algebra k K'] [IsScalarTower k K K'] in
theorem isScalarTower_ext (v : Place k K) : IsScalarTower v.ring K K' :=
  IsScalarTower.of_algebraMap_eq fun _ => rfl

attribute [local instance] isScalarTower_ext

omit [Algebra k K'] [IsScalarTower k K K'] in
theorem isTorsionFree_ext (v : Place k K) : Module.IsTorsionFree v.ring K' :=
  Module.isTorsionFree_iff_algebraMap_injective.2
    ((algebraMap K K').injective.comp (IsFractionRing.injective v.ring K))

attribute [local instance] isTorsionFree_ext

section Closure

variable [IsFunctionField k K] [FiniteDimensional K K'] [Algebra.IsSeparable K K'] (v : Place k K)

omit [Algebra k K'] [IsScalarTower k K K'] in
theorem isDedekindDomain_closure : IsDedekindDomain (integralClosure v.ring K') :=
  IsIntegralClosure.isDedekindDomain v.ring K K' _

omit [Algebra k K'] [IsScalarTower k K K'] [IsFunctionField k K] [Algebra.IsSeparable K K'] in
theorem isFractionRing_closure : IsFractionRing (integralClosure v.ring K') K' :=
  integralClosure.isFractionRing_of_finite_extension (A := v.ring) K K'

omit [Algebra k K'] [IsScalarTower k K K'] in
theorem finite_closure : Module.Finite v.ring (integralClosure v.ring K') :=
  IsIntegralClosure.finite v.ring K K' _

omit [Algebra k K'] [IsScalarTower k K K'] [IsFunctionField k K] [FiniteDimensional K K']
  [Algebra.IsSeparable K K'] in
theorem isTorsionFree_closure : Module.IsTorsionFree v.ring (integralClosure v.ring K') :=
  IsIntegralClosure.isTorsionFree v.ring K'

omit [Algebra k K'] [IsScalarTower k K K'] in
theorem finrank_closure :
    Module.finrank v.ring (integralClosure v.ring K') = Module.finrank K K' :=
  IsIntegralClosure.rank v.ring K K' _

attribute [local instance] isDedekindDomain_closure isFractionRing_closure finite_closure
  isTorsionFree_closure

end Closure

section Correspondence

variable [IsFunctionField k K] [FiniteDimensional K K'] [Algebra.IsSeparable K K'] (v : Place k K)

attribute [local instance] isDedekindDomain_closure isFractionRing_closure finite_closure
  isTorsionFree_closure

omit [Algebra k K'] [IsScalarTower k K K'] [FiniteDimensional K K'] [Algebra.IsSeparable K K'] in
theorem ne_bot_of_mem_primesOver {q : Ideal (integralClosure v.ring K')}
    (hq : q ∈ (maximalIdeal v.ring).primesOver (integralClosure v.ring K')) : q ≠ ⊥ := by
  intro h
  have hinj : Function.Injective (algebraMap v.ring (integralClosure v.ring K')) :=
    Module.isTorsionFree_iff_algebraMap_injective.1 (isTorsionFree_closure v)
  apply IsDiscreteValuationRing.not_a_field v.ring
  rw [hq.2.over, h]
  exact Ideal.comap_bot_of_injective _ hinj

noncomputable def primeHS (q : (maximalIdeal v.ring).primesOver (integralClosure v.ring K')) :
    HeightOneSpectrum (integralClosure v.ring K') :=
  ⟨q.1, q.2.1, v.ne_bot_of_mem_primesOver q.2⟩

omit [IsScalarTower k K K'] [IsFunctionField k K] [FiniteDimensional K K'] [Algebra.IsSeparable K K'] in

theorem mem_of_isIntegral_of_liesOver {w : Place k K'} (h : w.LiesOver v) {x : K'}
    (hx : IsIntegral v.ring x) : x ∈ w.ring := by
  let := h.algebra
  have : IsScalarTower v.ring w.ring K' := IsScalarTower.of_algebraMap_eq fun _ => rfl
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.1 (hx.tower_top (A := w.ring))
  rw [← hy]
  exact y.2

noncomputable abbrev placeOfPrime (q : (maximalIdeal v.ring).primesOver (integralClosure v.ring K')) :
    Place k K' where
  ring := HeightOneSpectrum.valuationSubringAtPrime K' (v.primeHS q)
  ne_top := by
    intro htop
    obtain ⟨π, hπ⟩ := (v.primeHS q).valuation_exists_uniformizer K'
    have hle := HeightOneSpectrum.valuationSubringAtPrime_le_valuation (K := K') (v := v.primeHS q)
    have hmem : π⁻¹ ∈ ((v.primeHS q).valuation K').valuationSubring :=
      hle (htop ▸ ValuationSubring.mem_top _)
    rw [Valuation.mem_valuationSubring_iff, map_inv₀, hπ, ← WithZero.exp_neg, ← WithZero.exp_zero,
      WithZero.exp_le_exp] at hmem
    omega
  algebraMap_mem c := by
    have hc : IsIntegral v.ring (algebraMap k K' c) := by
      rw [IsScalarTower.algebraMap_apply k K K']
      exact isIntegral_algebraMap (R := v.ring) (x := (⟨_, v.algebraMap_mem c⟩ : v.ring))
    exact Subalgebra.algebraMap_mem (Localization.subalgebra.ofField K' _
      (v.primeHS q).asIdeal.primeCompl_le_nonZeroDivisors)
      (⟨algebraMap k K' c, hc⟩ : integralClosure v.ring K')

theorem closure_mem_placeOfPrime (q : (maximalIdeal v.ring).primesOver (integralClosure v.ring K'))
    (b : integralClosure v.ring K') : (b : K') ∈ (v.placeOfPrime q).ring :=
  Subalgebra.algebraMap_mem (Localization.subalgebra.ofField K' _
    (v.primeHS q).asIdeal.primeCompl_le_nonZeroDivisors) b

theorem placeOfPrime_liesOver (q : (maximalIdeal v.ring).primesOver (integralClosure v.ring K')) :
    (v.placeOfPrime q).LiesOver v :=
  liesOver_of_le fun x hx =>
    v.closure_mem_placeOfPrime q (algebraMap v.ring (integralClosure v.ring K') ⟨x, hx⟩)

end Correspondence

section Sum

variable [IsFunctionField k K] [IsFunctionField k K'] [FiniteDimensional K K']
  [Algebra.IsSeparable K K'] (v : Place k K)

attribute [local instance] isDedekindDomain_closure isFractionRing_closure finite_closure
  isTorsionFree_closure

noncomputable def closureHom {w : Place k K'} (h : w.LiesOver v) :
    integralClosure v.ring K' →+* w.ring :=
  RingHom.codRestrict (algebraMap (integralClosure v.ring K') K') w.ring fun b =>
    v.mem_of_isIntegral_of_liesOver h ((mem_integralClosure_iff v.ring K').1 b.2)

noncomputable def primeOfPlace {w : Place k K'} (h : w.LiesOver v) :
    (maximalIdeal v.ring).primesOver (integralClosure v.ring K') :=
  ⟨(maximalIdeal w.ring).comap (v.closureHom h), Ideal.comap_isPrime _ _, ⟨by
    let := h.algebra
    have := h.isLocalHom
    have hc : (v.closureHom h).comp (algebraMap v.ring (integralClosure v.ring K')) =
        algebraMap v.ring w.ring := RingHom.ext fun a => Subtype.ext rfl
    change maximalIdeal v.ring = Ideal.comap (algebraMap v.ring (integralClosure v.ring K'))
      (Ideal.comap (v.closureHom h) (maximalIdeal w.ring))
    rw [Ideal.comap_comap, hc]
    have hlo : (maximalIdeal w.ring).LiesOver (maximalIdeal v.ring) := inferInstance
    exact hlo.over⟩⟩

theorem placeOfPrime_primeOfPlace {w : Place k K'} (h : w.LiesOver v) :
    v.placeOfPrime (v.primeOfPlace h) = w := by
  refine Place.eq_of_le fun x hx => ?_
  obtain ⟨a, s, hs, rfl⟩ := hx
  have ha : ((a : integralClosure v.ring K') : K') ∈ w.ring := (v.closureHom h a).2
  have hsw : ((s : integralClosure v.ring K') : K') ∈ w.ring := (v.closureHom h s).2
  have hs' : v.closureHom h s ∉ maximalIdeal w.ring := hs
  have hs1 : w.ring.valuation (s : K') = 1 :=
    le_antisymm (w.ring.valuation_le_one_iff _ |>.2 hsw) (not_lt.1 fun hlt =>
      hs' ((w.ring.valuation_lt_one_iff _).2 hlt))
  have hsinv : ((s : integralClosure v.ring K') : K')⁻¹ ∈ w.ring := by
    rw [← w.ring.valuation_le_one_iff, map_inv₀, hs1, inv_one]
  exact mul_mem ha hsinv

omit [IsFunctionField k K'] in
theorem primeOfPlace_placeOfPrime
    (q : (maximalIdeal v.ring).primesOver (integralClosure v.ring K')) :
    v.primeOfPlace (v.placeOfPrime_liesOver q) = q := by
  apply Subtype.ext
  ext b
  change v.closureHom _ b ∈ maximalIdeal (v.placeOfPrime q).ring ↔ b ∈ q.1
  rw [ValuationSubring.valuation_lt_one_iff]
  change (v.placeOfPrime q).ring.valuation (b : K') < 1 ↔ b ∈ q.1
  constructor
  · intro hb
    by_contra hbq
    have hinv : ((b : integralClosure v.ring K') : K')⁻¹ ∈ (v.placeOfPrime q).ring :=
      ⟨1, b, hbq, by simp⟩
    have hbmem := v.closure_mem_placeOfPrime q b
    have hb0 : (b : K') ≠ 0 := by
      intro h0
      rw [h0, inv_zero] at hinv
      exact hbq (by
        have : b = 0 := Subtype.ext h0
        rw [this]; exact q.1.zero_mem)
    have h1 := (v.placeOfPrime q).ring.valuation_le_one_iff _ |>.2 hinv
    rw [map_inv₀, inv_le_one₀ (zero_lt_iff.2 ((Valuation.ne_zero_iff _).2 hb0))] at h1
    exact absurd hb (not_lt.2 h1)
  · intro hbq
    by_contra hb
    have hb1 : (v.placeOfPrime q).ring.valuation (b : K') = 1 :=
      le_antisymm ((v.placeOfPrime q).ring.valuation_le_one_iff _ |>.2
        (v.closure_mem_placeOfPrime q b)) (not_lt.1 hb)
    have hb0 : (b : K') ≠ 0 := by
      intro h0; rw [h0, map_zero] at hb1; exact zero_ne_one hb1
    have hinv : ((b : integralClosure v.ring K') : K')⁻¹ ∈ (v.placeOfPrime q).ring := by
      rw [← ValuationSubring.valuation_le_one_iff, map_inv₀, hb1, inv_one]
    have hle := HeightOneSpectrum.valuationSubringAtPrime_le_valuation (K := K') (v := v.primeHS q)
    have h1 : (v.primeHS q).valuation K' (b : K')⁻¹ ≤ 1 := hle hinv
    have h2 : (v.primeHS q).valuation K' (algebraMap (integralClosure v.ring K') K' b) < 1 :=
      ((v.primeHS q).valuation_lt_one_iff_mem (K := K') b).2 hbq
    rw [map_inv₀, inv_le_one₀ (zero_lt_iff.2 ((Valuation.ne_zero_iff _).2 hb0))] at h1
    exact absurd h2 (not_lt.2 h1)

noncomputable def primesOverEquiv :
    (maximalIdeal v.ring).primesOver (integralClosure v.ring K') ≃
      {w : Place k K' // w.LiesOver v} where
  toFun q := ⟨v.placeOfPrime q, v.placeOfPrime_liesOver q⟩
  invFun w := v.primeOfPlace w.2
  left_inv q := v.primeOfPlace_placeOfPrime q
  right_inv w := Subtype.ext (v.placeOfPrime_primeOfPlace w.2)

theorem valuation_primeHS (q : (maximalIdeal v.ring).primesOver (integralClosure v.ring K')) :
    (v.primeHS q).valuation K' = (v.placeOfPrime q).valuation := by
  symm
  refine valuation_eq_of_isEquiv ?_ (v.placeOfPrime q).valuation_surjective
    (HeightOneSpectrum.valuation_surjective K' _)
  refine Valuation.isEquiv_iff_val_le_one.2 fun {x} => ?_
  rw [Place.valuation_le_one_iff]
  have hle := HeightOneSpectrum.valuationSubringAtPrime_le_valuation (K := K') (v := v.primeHS q)
  let P : Place k K' :=
    { ring := ((v.primeHS q).valuation K').valuationSubring
      ne_top := by
        intro htop
        obtain ⟨π, hπ⟩ := (v.primeHS q).valuation_exists_uniformizer K'
        have hmem : π⁻¹ ∈ ((v.primeHS q).valuation K').valuationSubring :=
          htop ▸ ValuationSubring.mem_top _
        rw [Valuation.mem_valuationSubring_iff, map_inv₀, hπ, ← WithZero.exp_neg,
          ← WithZero.exp_zero, WithZero.exp_le_exp] at hmem
        omega
      algebraMap_mem := fun c => hle ((v.placeOfPrime q).algebraMap_mem c) }
  have heq : v.placeOfPrime q = P := Place.eq_of_le hle
  constructor
  · intro hx
    exact hle hx
  · intro hx
    have hxP : x ∈ P.ring := hx
    rw [← heq] at hxP
    exact hxP

theorem ramificationIdx_primeOfPlace_eq
    (q : (maximalIdeal v.ring).primesOver (integralClosure v.ring K')) :
    q.1.ramificationIdx v.ring = (v.placeOfPrime q).ramificationIdx v := by
  have := q.2.1
  have := q.2.2
  have : (v.primeHS q).asIdeal.LiesOver v.heightOneSpectrum.asIdeal := q.2.2
  have hp : maximalIdeal v.ring ≠ ⊥ := IsDiscreteValuationRing.not_a_field v.ring
  have h := v.placeOfPrime_liesOver q
  rw [← Ideal.ramificationIdx'_eq_ramificationIdx (maximalIdeal v.ring) q.1 hp,
    ← h.ramificationIdx'_eq]
  have e1 : v.valuation v.uniformizer ^ (maximalIdeal v.ring).ramificationIdx' q.1 =
      (v.primeHS q).valuation K' (algebraMap K K' v.uniformizer) :=
    HeightOneSpectrum.valuation_liesOver K' v.heightOneSpectrum (v.primeHS q) v.uniformizer
  have e2 := h.valuation_algebraMap v.uniformizer
  rw [valuation_primeHS, ← e2, v.valuation_eq_exp_neg_ord v.uniformizer_ne_zero, v.ord_uniformizer,
    ← WithZero.exp_nsmul, ← WithZero.exp_nsmul, WithZero.exp_inj] at e1
  simpa using e1

omit [IsFunctionField k K'] in

theorem inertiaDeg_primeOfPlace_eq
    (q : (maximalIdeal v.ring).primesOver (integralClosure v.ring K')) :
    q.1.inertiaDeg v.ring = (v.placeOfPrime q).inertiaDeg v := by
  have := q.2.1
  have := q.2.2
  have hmax : q.1.IsMaximal := q.2.1.isMaximal (v.ne_bot_of_mem_primesOver q.2)
  have h := v.placeOfPrime_liesOver q
  rw [Ideal.inertiaDeg_eq_of_isMaximal (maximalIdeal v.ring) q.1, ← h.finrank_residueField]
  let := h.algebra
  have := h.isLocalHom
  have : IsLocalization.AtPrime (v.placeOfPrime q).ring q.1 :=
    inferInstanceAs (IsLocalization (v.primeHS q).asIdeal.primeCompl
      (HeightOneSpectrum.valuationSubringAtPrime K' (v.primeHS q)))
  refine Algebra.finrank_eq_of_equiv_equiv (RingEquiv.refl _)
    (IsLocalization.AtPrime.equivQuotMaximalIdeal q.1 (v.placeOfPrime q).ring) ?_
  apply Ideal.Quotient.ringHom_ext
  ext a
  rfl

theorem finite_liesOver : {w : Place k K' | w.LiesOver v}.Finite := by
  have hfin : ((maximalIdeal v.ring).primesOver (integralClosure v.ring K')).Finite :=
    Algebra.QuasiFinite.finite_primesOver _
  have := hfin.to_subtype
  exact Set.finite_coe_iff.1 (Finite.of_equiv _ v.primesOverEquiv)

theorem sum_ramificationIdx_mul_inertiaDeg :
    ∑ w ∈ (v.finite_liesOver (K' := K')).toFinset, w.ramificationIdx v * w.inertiaDeg v =
      Module.finrank K K' := by
  classical
  have hfin : ((maximalIdeal v.ring).primesOver (integralClosure v.ring K')).Finite :=
    Algebra.QuasiFinite.finite_primesOver _
  let : Fintype ((maximalIdeal v.ring).primesOver (integralClosure v.ring K')) := hfin.fintype
  let : Fintype {w : Place k K' // w.LiesOver v} := Fintype.ofEquiv _ v.primesOverEquiv
  have hsum := Ideal.sum_ramification_inertia_eq_finrank (maximalIdeal v.ring)
    (integralClosure v.ring K')
  rw [finrank_closure] at hsum
  have hs : ∀ w : Place k K', w ∈ (v.finite_liesOver (K' := K')).toFinset ↔ w.LiesOver v :=
    fun w => Set.Finite.mem_toFinset _
  rw [← hsum, Finset.sum_subtype _ hs]
  refine (Fintype.sum_equiv v.primesOverEquiv _ _ fun q => ?_).symm
  rw [ramificationIdx_primeOfPlace_eq, inertiaDeg_primeOfPlace_eq]
  rfl

noncomputable def heightOneSpectrumEquiv :
    {P : HeightOneSpectrum (integralClosure v.ring K') //
        P.asIdeal.LiesOver (maximalIdeal v.ring)} ≃
      (maximalIdeal v.ring).primesOver (integralClosure v.ring K') where
  toFun P := ⟨P.1.asIdeal, P.1.isPrime, P.2⟩
  invFun q := ⟨v.primeHS q, q.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

noncomputable def heightOneSpectrumEquivPlaces :
    {P : HeightOneSpectrum (integralClosure v.ring K') //
        P.asIdeal.LiesOver (maximalIdeal v.ring)} ≃ {w : Place k K' // w.LiesOver v} :=
  v.heightOneSpectrumEquiv.trans v.primesOverEquiv

end Sum

end Place

end GroundTheory.FunctionField
