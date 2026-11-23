import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.AdjKltOfLtDisc
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DOnEqZeroOfEqOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormOrdDFormNonneg
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DvrPlaceTopFormOrdersApi
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MinOrdLeOrdAdd
import ReciprocityTheory.CommutativeAlgebra.PolynomialHeights.HeightAddRingKrullDimQuotientMvPolynomialField
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumOrdSubOneLeOrdWedgeDifferentials
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsPlacePlane

set_option autoImplicit false

noncomputable section

open GlobalTheory.TopForm

namespace GlobalTheory.FieldPair.AdjModel

variable {k K : Type} [Field k] [Field K] {c : k →+* K} {n : ℕ}

def incl {Q : Subring K} {P : Place c} (h : P.Contains Q) : Q →+* P.ring :=
  Q.subtype.codRestrict P.ring fun q => h q q.2

theorem isUnit_of_ord_eq_zero (P : Place c) (b : P.ring) (hb : (b : K) ≠ 0)
    (h : P.ord (b : K) = 0) : IsUnit b := by
  have h1 : (b : K)⁻¹ ∈ P.ring :=
    (P.ord_nonneg_iff (inv_ne_zero hb)).1 (by rw [P.ord_inv, h]; rfl)
  exact IsUnit.of_mul_eq_one ⟨_, h1⟩ (Subtype.ext (mul_inv_cancel₀ hb))

theorem formallyEtale_incl {Q : Subring K} {P : Place c} (h : P.IsPrimeOf Q) :
    (incl h.1).FormallyEtale := by
  letI := (incl h.1).toAlgebra
  haveI : IsLocalization ((IsUnit.submonoid P.ring).comap (incl h.1)) P.ring := by
    rw [isLocalization_iff]
    refine ⟨fun y => y.2, fun f => ?_, fun {a b} e => ⟨1, ?_⟩⟩
    · obtain ⟨a, ha, b, hb, hb0, hbo, e⟩ := h.2 f f.2
      exact ⟨⟨⟨a, ha⟩, ⟨⟨b, hb⟩, isUnit_of_ord_eq_zero P ⟨b, h.1 b hb⟩ hb0 hbo⟩⟩, Subtype.ext e⟩
    · have : (a : K) = b := congrArg (fun z : P.ring => (z : K)) e
      rw [Subtype.ext this]
  exact Algebra.FormallyEtale.of_isLocalization ((IsUnit.submonoid P.ring).comap (incl h.1))

theorem isFreeGen_of_formallyEtale {A B : Type} [CommRing A] [CommRing B] {α : k →+* A}
    {β : k →+* B} {ρ : A →+* B} (hρ : ρ.FormallyEtale) (h : ρ.comp α = β) {x : Fin n → A}
    (hω : IsFreeGen A (dForm α x)) : IsFreeGen B (dForm β fun i => ρ (x i)) := by
  rw [← formMap_dForm ρ h]
  letI := α.toAlgebra
  letI := β.toAlgebra
  letI := ρ.toAlgebra
  haveI : IsScalarTower k A B := IsScalarTower.of_algebraMap_eq' h.symm
  haveI : Algebra.FormallyEtale A B := hρ
  exact hω.of_isBaseChange (isBaseChange_exteriorPower
    (KaehlerDifferential.isBaseChange_of_formallyEtale k A B) n)

theorem formOrd_eq_zero {Q : Subring K} (hQ : IsLocModel c Q) {x : Fin n → Q}
    (hx : IsFreeGen Q (dForm (c.codRestrict Q hQ.const_mem) x)) {P : Place c}
    (h : P.IsPrimeOf Q) : P.formOrd (dForm c fun i => (x i : K)) = 0 := by
  have h1 := isFreeGen_of_formallyEtale (β := P.const) (formallyEtale_incl h) rfl hx
  have h2 := P.formOrd_toRat h1
  rwa [show P.toRat n (dForm P.const fun i => incl h.1 (x i)) = dForm c fun i => (x i : K) from
    formMap_dForm (α := P.const) (β := c) P.ring.subtype rfl _] at h2

theorem exists_place {Q : Subring K} (hQ : IsLocModel c Q) {t : Q} (ht : Prime t) :
    ∃ S : Place c, S.IsPrimeOf Q ∧ S.ord (t : K) = 1 ∧
      ∀ P : Place c, P.IsPrimeOf Q → P.ring ≠ S.ring → P.ord (t : K) = 0 := by
  let c0 := c.codRestrict Q hQ.const_mem
  haveI : IsNoetherianRing Q := by
    letI := c0.toAlgebra
    haveI : Algebra.EssFiniteType k Q := hQ.essFiniteType
    exact Algebra.EssFiniteType.isNoetherianRing k Q
  haveI : IsFractionRing Q K := by
    refine IsFractionRing.of_field Q K fun z => ?_
    obtain ⟨a, ha, b, hb, hb0, e⟩ := hQ.frac z
    exact ⟨⟨a, ha⟩, ⟨b, hb⟩, eq_div_of_mul_eq hb0 e⟩
  let p : Ideal Q := Ideal.span {t}
  haveI : p.IsPrime := (Ideal.span_singleton_prime ht.ne_zero).2 ht
  have hp : p.primeCompl ≤ nonZeroDivisors Q := p.primeCompl_le_nonZeroDivisors
  let A : Subalgebra Q K := Localization.subalgebra.ofField K p.primeCompl hp
  haveI hA : IsLocalization p.primeCompl A := Localization.subalgebra.isLocalization_ofField K _ hp
  haveI : IsLocalRing A := IsLocalization.AtPrime.isLocalRing A p
  haveI : IsNoetherianRing A := IsLocalization.isNoetherianRing p.primeCompl A inferInstance
  have hm : IsLocalRing.maximalIdeal A = Ideal.span {algebraMap Q A t} := by
    rw [← IsLocalization.AtPrime.map_eq_maximalIdeal p A, Ideal.map_span, Set.image_singleton]
  have ht0 : algebraMap Q A t ≠ 0 := fun e => ht.ne_zero (Subtype.ext (congrArg (fun z : A => (z : K)) e))
  have hnf : ¬ IsField A := fun hf => ht0 (by
    have := IsLocalRing.isField_iff_maximalIdeal_eq.1 hf
    rw [hm] at this
    exact Ideal.span_singleton_eq_bot.1 this)
  haveI : IsDiscreteValuationRing A :=
    ((IsDiscreteValuationRing.TFAE A hnf).out 0 4).2 (show (IsLocalRing.maximalIdeal A).IsPrincipal from ⟨_, hm⟩)
  haveI : IsFractionRing A K := Localization.subalgebra.isFractionRing_ofField K _ hp
  let V : ValuationSubring K :=
    { A.toSubring with
      mem_or_inv_mem' := fun x => by
        rcases ValuationRing.isInteger_or_isInteger A x with ⟨a, e⟩ | ⟨a, e⟩
        · exact Or.inl (e ▸ a.2)
        · exact Or.inr (e ▸ a.2) }
  have hc : ∀ a, c a ∈ V := fun a => A.algebraMap_mem (c0 a)
  let S : Place c := ⟨V, hc, ‹IsDiscreteValuationRing A›, by
    have e : c.codRestrict V hc = (algebraMap Q A).comp c0 := rfl
    rw [e]
    exact RingHom.EssFiniteType.comp hQ.essFiniteType
      ((RingHom.essFiniteType_algebraMap (R := Q) (S := A)).2
        (Algebra.EssFiniteType.of_isLocalization A p.primeCompl))⟩
  have hu : ∀ b : Q, b ∉ p → IsUnit (algebraMap Q A b) := fun b hb =>
    IsLocalization.map_units A (⟨b, hb⟩ : p.primeCompl)
  refine ⟨S, ⟨fun q hq => A.algebraMap_mem ⟨q, hq⟩, fun f hf => ?_⟩, ?_, fun P hP hne => ?_⟩
  · obtain ⟨⟨a, b⟩, e⟩ := IsLocalization.surj p.primeCompl (⟨f, hf⟩ : A)
    exact ⟨a, a.2, b.1, b.1.2, fun h => b.2 (by rw [show b.1 = 0 from Subtype.ext h]; exact p.zero_mem),
      S.ord_eq_zero (u := algebraMap Q A b.1) (hu _ b.2), congrArg Subtype.val e⟩
  · exact S.ord_irreducible (t := algebraMap Q A t)
      ((IsDiscreteValuationRing.irreducible_iff_uniformizer _).2 hm)
  · by_contra h0
    have htK : (t : K) ≠ 0 := fun e => ht.ne_zero (Subtype.ext e)
    have h1 : 0 ≤ P.ord (t : K) := (P.ord_nonneg_iff htK).2 (hP.1 _ t.2)
    refine hne (ValuationSubring.eq_of_le_of_ne_top P.ring (fun f hf => ?_) S.ring_ne_top)
    obtain ⟨a, ha, b, hb, hb0, hbo, e⟩ := hP.2 f hf
    have hbp : (⟨b, hb⟩ : Q) ∉ p := fun h => by
      obtain ⟨d, hd⟩ := Ideal.mem_span_singleton.1 h
      have hd' : b = t * d := congrArg Subtype.val hd
      have hd0 : (d : K) ≠ 0 := fun h => hb0 (by rw [hd', h, mul_zero])
      have := (P.ord_nonneg_iff hd0).2 (hP.1 _ d.2)
      rw [hd', P.ord_mul htK hd0] at hbo
      omega
    obtain ⟨g, hg⟩ := (hu _ hbp).exists_right_inv
    have hg' : b * (g : K) = 1 := congrArg Subtype.val hg
    have : f = a * g := by rw [← e, mul_assoc, hg', mul_one]
    rw [this]
    exact A.mul_mem (A.algebraMap_mem ⟨a, ha⟩) g.2

open MvPolynomial in

theorem exists_plane (k : Type) [Field k] :
    ∃ (Q : Subring (FractionRing (MvPolynomial (Fin 2) k)))
      (hQ : IsLocModel (algebraMap k _) Q) (x : Fin 2 → Q),
      (∀ i, (x i : FractionRing (MvPolynomial (Fin 2) k)) =
        algebraMap (MvPolynomial (Fin 2) k) _ (X i)) ∧
      Ideal.span {x 0, x 1} = (letI := hQ.isLocalRing; IsLocalRing.maximalIdeal Q) ∧
      ringKrullDim Q = 2 ∧ (∀ i, Prime (x i)) ∧
      IsFreeGen Q (dForm ((algebraMap k _).codRestrict Q hQ.const_mem) x) := by
  let P := MvPolynomial (Fin 2) k
  let L := FractionRing P
  let q : Ideal P := RingHom.ker (constantCoeff : P →+* k)
  have hs : Function.Surjective (constantCoeff : P →+* k) := fun a => ⟨C a, constantCoeff_C _ a⟩
  haveI : q.IsMaximal := RingHom.ker_isMaximal_of_surjective _ hs
  have hq : q.primeCompl ≤ nonZeroDivisors P := q.primeCompl_le_nonZeroDivisors
  let A : Subalgebra P L := Localization.subalgebra.ofField L q.primeCompl hq
  haveI hA : IsLocalization q.primeCompl A := Localization.subalgebra.isLocalization_ofField L _ hq
  let a : P →+* A := algebraMap P A
  have hc : ∀ x, algebraMap k L x ∈ A.toSubring := fun x => A.algebraMap_mem (C x)
  have e : (algebraMap k L).codRestrict A.toSubring hc = a.comp (algebraMap k P) := rfl
  haveI := IsLocalization.AtPrime.isLocalRing A q
  have hX : ∀ i, X i ∈ q := fun i => constantCoeff_X k i
  have hsp : q = Ideal.span {X 0, X 1} := by
    refine le_antisymm (fun f hf => ?_) (Ideal.span_le.2 ?_)
    · have : (({X 0, X 1} : Set P)) = X '' (Set.univ : Set (Fin 2)) := by
        ext z; simp [eq_comm]
      rw [this, mem_ideal_span_X_image]
      intro m hm
      by_contra hc
      push Not at hc
      have : m = 0 := Finsupp.ext fun i => hc i trivial
      subst this
      exact (mem_support_iff.1 hm) hf
    · rintro _ (rfl | rfl) <;> exact hX _
  refine ⟨A.toSubring, ⟨hc, ‹IsLocalRing A›, ?_, ?_⟩, fun i => a (X i), fun _ => rfl, ?_, ?_,
    fun i => ?_, ?_⟩
  · rw [e]
    refine RingHom.EssFiniteType.comp ?_ ?_
    · exact RingHom.essFiniteType_algebraMap.2 (inferInstance : Algebra.EssFiniteType k P)
    · exact (RingHom.essFiniteType_algebraMap (R := P) (S := A)).2
        (Algebra.EssFiniteType.of_isLocalization A q.primeCompl)
  · intro f
    obtain ⟨x, y, hy, rfl⟩ := IsFractionRing.div_surjective (A := P) f
    have hy' : algebraMap P L y ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hy
    exact ⟨_, A.algebraMap_mem x, _, A.algebraMap_mem y, hy', div_mul_cancel₀ _ hy'⟩
  · change (Ideal.span {a (X 0), a (X 1)} : Ideal A) = IsLocalRing.maximalIdeal A
    rw [← IsLocalization.AtPrime.map_eq_maximalIdeal q A]
    conv_rhs => rw [hsp]
    rw [Ideal.map_span, Set.image_pair]
  · change ringKrullDim A = 2
    have h := ReciprocityTheory.CA.height_add_ringKrullDim_quotient_mvPolynomial_field k 2 q
    rw [ringKrullDim_eq_zero_of_isField ((Ideal.Quotient.maximal_ideal_iff_isField_quotient q).1 ‹_›), add_zero] at h
    rw [IsLocalization.AtPrime.ringKrullDim_eq_height q A, h]
    rfl
  · change Prime (a (X i))
    have h0 : a (X i) ≠ 0 := fun h => X_ne_zero i
      (IsFractionRing.injective P L ((congrArg (fun z : A => (z : L)) h).trans (map_zero _).symm))
    have hp : (Ideal.span {(X i : P)}).IsPrime :=
      (Ideal.span_singleton_prime (X_ne_zero i)).2 X_prime
    have := IsLocalization.isPrime_of_isPrime_disjoint q.primeCompl A _ hp
      (Set.disjoint_left.2 fun z hz hz' => hz (Ideal.span_le.2 (by simpa using hX i) hz'))
    rw [Ideal.map_span, Set.image_singleton] at this
    exact (Ideal.span_singleton_prime h0).1 this
  · exact isFreeGen_of_formallyEtale (α := algebraMap k P) (ρ := a)
      (RingHom.formallyEtale_algebraMap.2 (Algebra.FormallyEtale.of_isLocalization q.primeCompl))
      rfl (isFreeGen_dForm_X k 2)

theorem sum_ord_sub_one_le [PerfectField k] {x : Fin n → K} (hx : TrBasis c x)
    (h0 : dForm c x ≠ 0) (hx0 : ∀ i, x i ≠ 0) (E : Place c) :
    ∑ i, E.ord (x i) - 1 ≤ E.formOrd (dForm c x) := by
  classical
  letI := c.toAlgebra
  letI := E.const.toAlgebra
  haveI : IsScalarTower k E.ring K := IsScalarTower.of_algebraMap_eq' rfl
  have hη : dForm c x = dWedge k x := rfl
  obtain ⟨t, ht⟩ := IsDiscreteValuationRing.exists_irreducible E.ring
  have ht0 : algebraMap E.ring K t ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective E.ring K)).mpr ht.ne_zero
  obtain ⟨γ, hγ⟩ := GlobalTheory.smul_dlogWedge_mem_regForms k t ht0 Finset.univ x
    (fun i _ => GlobalTheory.exists_eq_unit_mul_zpow ht (hx0 i))
    (fun i hi => (hi (Finset.mem_univ i)).elim)
  obtain ⟨ω, hω⟩ := E.exists_isFreeGen hx
  obtain ⟨a, rfl⟩ := hω.2 γ
  have hbr : ∀ θ, GlobalTheory.formMap k E.ring K n θ = E.toRat n θ := fun _ => rfl
  have hPne : (∏ i, x i) ≠ 0 := Finset.prod_ne_zero_iff.2 fun i _ => hx0 i
  have h2 : dWedge k x = (∏ i, x i) • dlogWedge k Finset.univ x := by
    rw [GlobalTheory.dlogWedge_eq_smul, smul_smul, mul_inv_cancel₀ hPne, one_smul]
  have h3 : (algebraMap E.ring K t) • dlogWedge k Finset.univ x =
      (algebraMap E.ring K a) • E.toRat n ω := by
    calc (algebraMap E.ring K t) • dlogWedge k Finset.univ x = t • dlogWedge k Finset.univ x :=
          algebraMap_smul _ t _
      _ = GlobalTheory.formMap k E.ring K n (a • ω) := hγ.symm
      _ = a • E.toRat n ω := by rw [map_smul, hbr]
      _ = (algebraMap E.ring K a) • E.toRat n ω := (algebraMap_smul _ a _).symm
  have key : dForm c x =
      ((∏ i, x i) * (algebraMap E.ring K t)⁻¹ * algebraMap E.ring K a) • E.toRat n ω := by
    rw [hη, h2, mul_assoc, mul_smul, mul_smul, ← h3, inv_smul_smul₀ ht0]
  have ha0 : algebraMap E.ring K a ≠ 0 := by
    intro h
    apply h0
    rw [key, h, mul_zero, zero_smul]
  have hsum : ∀ s : Finset (Fin n), E.ord (∏ j ∈ s, x j) = ∑ j ∈ s, E.ord (x j) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | insert j s hj ih =>
      rw [Finset.prod_insert hj, Finset.sum_insert hj,
        E.ord_mul (hx0 j) (Finset.prod_ne_zero_iff.2 fun i _ => hx0 i), ih]
  have hordt : E.ord (algebraMap E.ring K t) = 1 := E.ord_irreducible ht
  have horda : 0 ≤ E.ord (algebraMap E.ring K a) := (E.ord_nonneg_iff ha0).2 a.2
  rw [key, E.formOrd_smul_toRat hω (mul_ne_zero (mul_ne_zero hPne (inv_ne_zero ht0)) ha0),
    E.ord_mul (mul_ne_zero hPne (inv_ne_zero ht0)) ha0, E.ord_mul hPne (inv_ne_zero ht0),
    E.ord_inv, hsum, hordt]
  omega

theorem mem_maximalIdeal_iff (P : Place c) (b : P.ring) (hb : (b : K) ≠ 0) :
    b ∈ IsLocalRing.maximalIdeal P.ring ↔ P.ord (b : K) ≠ 0 :=
  ⟨fun h h0 => h (isUnit_of_ord_eq_zero P b hb h0), fun h hu => h (P.ord_eq_zero hu)⟩

theorem neighbour_ne {Q : Subring K} (hQ : IsLocModel c Q) {t u : Q} {S E : Place c}
    (hm : Ideal.span {t, u} = (letI := hQ.isLocalRing; IsLocalRing.maximalIdeal Q))
    (hd : ringKrullDim Q = 2) (hS : S.IsPrimeOf Q) (ht : S.ord (t : K) = 1)
    (hu : E.ord (u : K) = 1) : E ≠ S := by
  rintro rfl
  haveI := hQ.isLocalRing
  have h0 : E.ord (0 : K) = 0 := by simp [Place.ord]
  have hle : IsLocalRing.maximalIdeal Q ≤
      (IsLocalRing.maximalIdeal E.ring).comap (incl hS.1) := by
    rw [← hm, Ideal.span_le]
    rintro _ (h | h) <;> rw [h]
    · exact (mem_maximalIdeal_iff E _ fun h => by
        change (t : K) = 0 at h; rw [h, h0] at ht; omega).2 (by change E.ord (t : K) ≠ 0; omega)
    · exact (mem_maximalIdeal_iff E _ fun h => by
        change (u : K) = 0 at h; rw [h, h0] at hu; omega).2 (by change E.ord (u : K) ≠ 0; omega)
  have hb : Function.Bijective (incl hS.1) := by
    refine ⟨fun a b e => Subtype.ext (congrArg (fun z : E.ring => (z : K)) e), fun f => ?_⟩
    obtain ⟨a, ha, b, hb, hb0, hbo, e⟩ := hS.2 f f.2
    have hu : IsUnit (⟨b, hb⟩ : Q) := by
      by_contra hn
      exact (mem_maximalIdeal_iff E _ hb0).1 (hle hn) hbo
    obtain ⟨g, hg⟩ := hu.exists_right_inv
    have hg' : b * (g : K) = 1 := congrArg Subtype.val hg
    refine ⟨⟨a, ha⟩ * g, Subtype.ext ?_⟩
    change a * (g : K) = f
    rw [← e, mul_assoc, hg', mul_one]
  have := ringKrullDim_eq_of_ringEquiv (RingEquiv.ofBijective _ hb)
  rw [hd, IsPrincipalIdealRing.ringKrullDim_eq_one _ (IsDiscreteValuationRing.not_isField _)] at this
  exact absurd this (by decide)

theorem eq_of_centre {Q : Subring K} (hQ : IsLocModel c Q) {t u : Q} {S E : Place c}
    (hu : ¬ IsUnit u) (hu0 : (u : K) ≠ 0) (hd : ringKrullDim Q = 2) (hp : Prime t)
    (hS : S.IsPrimeOf Q) (ht : S.ord (t : K) = 1) (hE : E.Contains Q)
    (h1 : E.ord (t : K) ≠ 0) (h2 : E.ord (u : K) = 0) : E = S := by
  haveI := hQ.isLocalRing
  have ht0 : (t : K) ≠ 0 := fun e => hp.ne_zero (Subtype.ext e)
  let p : Ideal Q := (IsLocalRing.maximalIdeal E.ring).comap (incl hE)
  haveI hpp : p.IsPrime := Ideal.comap_isPrime _ _
  haveI hp1 : (Ideal.span {t}).IsPrime := (Ideal.span_singleton_prime hp.ne_zero).2 hp
  have l1 : Ideal.span {t} ≤ p := Ideal.span_le.2 (by
    rintro _ h
    rw [h]
    exact (mem_maximalIdeal_iff E (incl hE t) ht0).2 h1)
  have l2 : p < IsLocalRing.maximalIdeal Q :=
    lt_of_le_of_ne (IsLocalRing.le_maximalIdeal hpp.ne_top) fun e =>
      (mem_maximalIdeal_iff E (incl hE u) hu0).1 (show u ∈ p from e ▸ hu) h2
  have l0 : (⊥ : Ideal Q) < Ideal.span {t} :=
    bot_lt_iff_ne_bot.2 fun e => hp.ne_zero (Ideal.span_singleton_eq_bot.1 e)
  have e1 : Ideal.span {t} = p := by
    by_contra hne
    have l1' := lt_of_le_of_ne l1 hne
    let s : LTSeries (PrimeSpectrum Q) := LTSeries.mk 3
      ![⟨⊥, inferInstance⟩, ⟨Ideal.span {t}, hp1⟩, ⟨p, hpp⟩,
        ⟨IsLocalRing.maximalIdeal Q, inferInstance⟩]
      (Fin.strictMono_iff_lt_succ.2 fun i => by
        fin_cases i
        exacts [l0, l1', l2])
    have := Order.LTSeries.length_le_krullDim s
    change ((3 : ℕ) : WithBot ℕ∞) ≤ ringKrullDim Q at this
    rw [hd] at this
    exact absurd this (by decide)
  refine Place.ext (ValuationSubring.eq_of_le_of_ne_top S.ring (fun f hf => ?_) E.ring_ne_top).symm
  obtain ⟨a, ha, b, hb, hb0, hbo, e⟩ := hS.2 f hf
  have hbp : (⟨b, hb⟩ : Q) ∉ p := fun h => by
    rw [← e1] at h
    obtain ⟨d, hd⟩ := Ideal.mem_span_singleton.1 h
    have hd' : b = t * d := congrArg Subtype.val hd
    have hd0 : (d : K) ≠ 0 := fun h => hb0 (by rw [hd', h, mul_zero])
    have := (S.ord_nonneg_iff hd0).2 (hS.1 _ d.2)
    rw [hd', S.ord_mul ht0 hd0] at hbo
    omega
  have hu : IsUnit (incl hE ⟨b, hb⟩) := by
    by_contra hn
    exact hbp hn
  obtain ⟨g, hg⟩ := hu.exists_right_inv
  have hg' : b * (g : K) = 1 := congrArg (fun z : E.ring => (z : K)) hg
  have : f = a * g := by rw [← e, mul_assoc, hg', mul_one]
  rw [this]
  exact E.ring.mul_mem _ _ (hE a ha) g.2

theorem plane_threshold (k : Type) [Field k] [CharZero k] :
    ∃ (K : Type) (_ : Field K) (c : k →+* K) (Q : Subring K) (S : Place c) (x : Fin 2 → K),
      IsLocModel c Q ∧ TrBasis c x ∧ dForm c x ≠ 0 ∧ S.IsPrimeOf Q ∧ S.ord (x 0) = 1 ∧
      (∀ i, x i ≠ 0) ∧
      (∀ s : ℚ, S.disc (dForm c x) (Finsupp.single (x 0) 1 + Finsupp.single (x 1) s) = -1 ∧
        ¬ Klt c 2 Q (dForm c x) (Finsupp.single (x 0) 1 + Finsupp.single (x 1) s) ∧
        (AdjKlt c 2 Q S (dForm c x) (Finsupp.single (x 0) 1 + Finsupp.single (x 1) s) ↔ s < 1)) ∧
      ∃ (hQ : IsLocModel c Q) (t u : Q) (E : Place c),
        Ideal.span {t, u} = (letI := hQ.isLocalRing; IsLocalRing.maximalIdeal Q) ∧
        ringKrullDim Q = 2 ∧ E.IsPrimeOf Q ∧ (t : K) = x 0 ∧ (u : K) = x 1 ∧ E.ord (x 1) = 1 ∧
        ∀ P : Place c, P.IsPrimeOf Q → P.ring ≠ E.ring → P.ord (x 1) = 0 := by
  obtain ⟨Q, hQ, x, hx, hm, hd, hp, hω⟩ := exists_plane k
  obtain ⟨S, hS, hS1, hS0⟩ := exists_place hQ (hp 0)
  obtain ⟨E, hE, hE1, hE0⟩ := exists_place hQ (hp 1)
  have htr : TrBasis (algebraMap k _) fun i => (x i : FractionRing (MvPolynomial (Fin 2) k)) := by
    rw [funext hx]
    exact trBasis_fractionRing 2
  have hx0 : ∀ i, (x i : FractionRing (MvPolynomial (Fin 2) k)) ≠ 0 :=
    fun i e => (hp i).ne_zero (Subtype.ext e)
  have hη : dForm (algebraMap k _) (fun i => (x i : FractionRing (MvPolynomial (Fin 2) k))) ≠ 0 :=
    fun h => one_ne_zero ((formOrd_api _ 2 _ htr).1.1 (a₁ := 1) (a₂ := 0) (by simp [h]))
  have hne : E ≠ S := neighbour_ne hQ hm hd hS hS1 hE1
  have hne' : E.ring ≠ S.ring := fun e => hne (Place.ext e)
  have hdisc : ∀ (P : Place (algebraMap k (FractionRing (MvPolynomial (Fin 2) k)))) (s : ℚ),
      P.disc (dForm _ fun i => (x i : FractionRing (MvPolynomial (Fin 2) k)))
        (Finsupp.single (x 0).1 1 + Finsupp.single (x 1).1 s) =
      P.formOrd (dForm _ fun i => (x i : FractionRing (MvPolynomial (Fin 2) k))) -
        (P.ord (x 0).1 + s * P.ord (x 1).1) := fun P s => by
    rw [Place.disc, map_add, Place.ordQ_single, Place.ordQ_single, one_mul]
  have hSd : ∀ s : ℚ, S.disc (dForm _ fun i => (x i : FractionRing (MvPolynomial (Fin 2) k)))
      (Finsupp.single (x 0).1 1 + Finsupp.single (x 1).1 s) = -1 := fun s => by
    rw [hdisc, formOrd_eq_zero hQ hω hS, hS1, hE0 S hS hne'.symm]
    simp
  refine ⟨_, _, _, Q, S, fun i => x i, hQ, htr, hη, hS, hS1, hx0, fun s => ⟨hSd s,
    fun h => (h.lt_disc hS.1).ne' (hSd s), fun h => ?_, fun hs => ?_⟩,
    hQ, x 0, x 1, E, hm, hd, hE, rfl, rfl, hE1, hE0⟩
  · replace h := by first | exact h.2.2 | exact h
    have := h Q hQ (x 0) (x 1) E le_rfl hm hd hS hE hS1 hE1 fun P hP h1 h2 => by
      rw [hdisc, formOrd_eq_zero hQ hω hP, hS0 P hP h1, hE0 P hP h2]
      simp
    rw [hdisc, formOrd_eq_zero hQ hω hE, hE1, hS0 E hE hne'] at this
    push_cast at this
    linarith
  · first
      | refine ⟨hη, by simp [Finsupp.single_eq_of_ne (hx0 0).symm,
          Finsupp.single_eq_of_ne (hx0 1).symm], ?_⟩
      | skip
    intro Q' hQ' t u F hle hm' hd' hS' hF ht hu _
    have hFS := neighbour_ne hQ' hm' hd' hS' ht hu
    have hFQ : F.Contains Q := hF.1.mono hle
    have a0 := (F.ord_nonneg_iff (hx0 0)).2 (hFQ _ (x 0).2)
    have a1 := (F.ord_nonneg_iff (hx0 1)).2 (hFQ _ (x 1).2)
    have b0 := Place.formOrd_dForm_nonneg _ 2 _ F htr fun i => hFQ _ (x i).2
    have b1 := sum_ord_sub_one_le htr hη hx0 F
    rw [Fin.sum_univ_two] at b1
    rw [hdisc]
    by_cases h1 : F.ord (x 1).1 = 0
    · have h0 : F.ord (x 0).1 = 0 := by
        by_contra h0
        exact hFS (eq_of_centre hQ (hp 1).not_unit (hx0 1) hd (hp 0) hS hS1 hFQ h0 h1)
      rw [h0, h1]
      have : (0 : ℚ) ≤ _ := Int.cast_nonneg b0
      push_cast
      linarith
    · have c1 : (0 : ℚ) < F.ord (x 1).1 := by exact_mod_cast lt_of_le_of_ne a1 (Ne.symm h1)
      have c2 := (Int.cast_le (R := ℚ)).2 b1
      push_cast at c2
      nlinarith

end GlobalTheory.FieldPair.AdjModel
