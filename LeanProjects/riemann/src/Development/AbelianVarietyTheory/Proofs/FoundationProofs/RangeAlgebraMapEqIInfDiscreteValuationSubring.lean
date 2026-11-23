import Mathlib

open IsLocalRing

namespace GlobalTheory

section KrullAkizuki

variable {A B : Type*} [CommRing A] [IsDomain A] [IsNoetherianRing A] [Ring.DimensionLEOne A]

theorem isArtinianRing_quotient_of_dimensionLEOne {I : Ideal A} (hI : I ≠ ⊥) :
    IsArtinianRing (A ⧸ I) := by
  rw [isArtinianRing_iff_krullDimLE_zero, Ring.krullDimLE_zero_iff]
  intro p hp
  have h1 : (p.comap (Ideal.Quotient.mk I)).IsMaximal := by
    refine Ring.DimensionLEOne.maximalOfPrime ?_ inferInstance
    intro h
    apply hI
    rw [eq_bot_iff, ← h]
    intro x hx
    simp [Ideal.mem_comap, Ideal.Quotient.eq_zero_iff_mem.mpr hx]
  have h2 := Ideal.map_comap_of_surjective (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective p
  rcases Ideal.map_eq_top_or_isMaximal_of_surjective (Ideal.Quotient.mk I)
    Ideal.Quotient.mk_surjective h1 with h | h
  · exact absurd (h2 ▸ h) hp.ne_top
  · exact h2 ▸ h

variable [CommRing B] [IsDomain B] [Algebra A B] [FaithfulSMul A B]

theorem finite_quotient_span_of_birational
    (hB : ∀ x : B, ∃ c : A, c ≠ 0 ∧ ∃ b : A, algebraMap A B c * x = algebraMap A B b)
    {a : A} (ha : a ≠ 0) : Module.Finite A (B ⧸ Ideal.span {algebraMap A B a}) := by
  set α := algebraMap A B a with hα
  have hα0 : α ≠ 0 := by simpa [hα] using ha
  have hart : IsArtinianRing (A ⧸ Ideal.span {a}) :=
    isArtinianRing_quotient_of_dimensionLEOne (by simpa using ha)
  let J : ℕ →o (Submodule (A ⧸ Ideal.span {a}) (A ⧸ Ideal.span {a}))ᵒᵈ :=
    ⟨fun n => OrderDual.toDual
      (((Ideal.span {α ^ n}).comap (algebraMap A B)).map (Ideal.Quotient.mk (Ideal.span {a}))),
      fun m n hmn => by
        apply OrderDual.toDual_le_toDual.mpr
        exact Ideal.map_mono (Ideal.comap_mono
          (Ideal.span_singleton_le_span_singleton.mpr (pow_dvd_pow α hmn)))⟩
  obtain ⟨n, hn⟩ := IsArtinian.monotone_stabilizes J
  let P : ℕ → B → Prop := fun h x => ∃ (u : B) (v : A), α ^ h * x = α ^ (h + 1) * u + algebraMap A B v
  have up : ∀ h x, P h x → P (h + 1) x := by
    rintro h x ⟨u, v, e⟩
    refine ⟨u, a * v, ?_⟩
    rw [map_mul, ← hα]
    linear_combination α * e
  have down : ∀ h x, n ≤ h → P (h + 1) x → P h x := by
    rintro h x hh ⟨u, v, e⟩
    have h1 : J (h + 1) = J (h + 2) := (hn _ (by omega)).symm.trans (hn _ (by omega))
    have h2 : ((Ideal.span {α ^ (h + 1)}).comap (algebraMap A B)).map
        (Ideal.Quotient.mk (Ideal.span {a})) = ((Ideal.span {α ^ (h + 2)}).comap
        (algebraMap A B)).map (Ideal.Quotient.mk (Ideal.span {a})) := OrderDual.toDual.injective h1
    have h3 : v ∈ (Ideal.span {α ^ (h + 1)}).comap (algebraMap A B) := by
      rw [Ideal.mem_comap, Ideal.mem_span_singleton]
      exact ⟨x - α * u, by linear_combination -e⟩
    have h4 := Ideal.mem_map_of_mem (Ideal.Quotient.mk (Ideal.span {a})) h3
    rw [h2, Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective] at h4
    obtain ⟨w, hw, hwv⟩ := h4
    rw [Ideal.mem_comap, Ideal.mem_span_singleton] at hw
    obtain ⟨z, hz⟩ := hw
    rw [eq_comm, Ideal.Quotient.eq, Ideal.mem_span_singleton] at hwv
    obtain ⟨t, ht⟩ := hwv
    have ht' := congrArg (algebraMap A B) ht
    rw [map_sub, map_mul, ← hα] at ht'
    refine ⟨u + z, t, mul_left_cancel₀ hα0 ?_⟩
    linear_combination e + ht' + hz
  have hP : ∀ x, P n x := by
    intro x
    obtain ⟨c, hc, b, hb⟩ := hB x
    have hart' : IsArtinianRing (A ⧸ Ideal.span {c}) :=
      isArtinianRing_quotient_of_dimensionLEOne (by simpa using hc)
    obtain ⟨h, y, hy⟩ := IsArtinian.exists_pow_succ_smul_dvd
      (Ideal.Quotient.mk (Ideal.span {c}) a) (1 : A ⧸ Ideal.span {c})
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective y
    simp only [smul_eq_mul, mul_one, ← map_pow, ← map_mul] at hy
    rw [eq_comm, Ideal.Quotient.eq, Ideal.mem_span_singleton] at hy
    obtain ⟨s, hs⟩ := hy
    have hs' := congrArg (algebraMap A B) hs
    simp only [map_sub, map_mul, map_pow, ← hα, Nat.succ_eq_add_one] at hs'
    have h0 : P h x := ⟨algebraMap A B r * x, b * s, by
      rw [map_mul]
      linear_combination x * hs' + algebraMap A B s * hb⟩
    have h1 : ∀ k, P (h + k) x := by
      intro k
      induction k with
      | zero => exact h0
      | succ k ih => exact up _ _ ih
    have h2 : ∀ k, P (n + k) x → P n x := by
      intro k
      induction k with
      | zero => exact id
      | succ k ih => exact fun hk => ih (down _ _ (Nat.le_add_right _ _) hk)
    exact h2 h (add_comm h n ▸ h1 n)
  let f : B →ₗ[A] B := LinearMap.mulLeft A (α ^ n)
  have hf : Function.Injective f := fun x y hxy => mul_left_cancel₀ (pow_ne_zero n hα0) hxy
  let N : Submodule A B := (Submodule.span A {(1 : B)}).comap f
  have hN : N.FG := by
    refine Submodule.fg_of_fg_map_injective f hf ?_
    exact Submodule.FG.of_le (Submodule.fg_span_singleton _) (Submodule.map_comap_le _ _)
  refine ⟨?_⟩
  have := hN.map (Ideal.Quotient.mkₐ A (Ideal.span {α})).toLinearMap
  suffices h : N.map (Ideal.Quotient.mkₐ A (Ideal.span {α})).toLinearMap = ⊤ from h ▸ this
  rw [eq_top_iff]
  intro y _
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective y
  obtain ⟨u, v, e⟩ := hP x
  refine ⟨x - α * u, ?_, ?_⟩
  · change α ^ n * (x - α * u) ∈ Submodule.span A {(1 : B)}
    rw [Submodule.mem_span_singleton]
    refine ⟨v, ?_⟩
    rw [← Algebra.algebraMap_eq_smul_one]
    linear_combination -e
  · change Ideal.Quotient.mk _ _ = _
    rw [Ideal.Quotient.eq, Ideal.mem_span_singleton]
    exact ⟨-u, by ring⟩

theorem krullAkizuki_of_birational
    (hB : ∀ x : B, ∃ c : A, c ≠ 0 ∧ ∃ b : A, algebraMap A B c * x = algebraMap A B b) :
    IsNoetherianRing B ∧ Ring.DimensionLEOne B := by
  have key : ∀ I : Ideal B, I ≠ ⊥ → ∃ a : A, a ≠ 0 ∧ algebraMap A B a ∈ I := by
    intro I hI
    obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hI
    obtain ⟨c, hc, b, hb⟩ := hB x
    refine ⟨b, ?_, hb ▸ I.mul_mem_left _ hx⟩
    rintro rfl
    simp [hc, hx0] at hb
  constructor
  · rw [isNoetherianRing_iff_ideal_fg]
    intro I
    rcases eq_or_ne I ⊥ with rfl | hI
    · exact Submodule.fg_bot
    obtain ⟨a, ha, haI⟩ := key I hI
    have h1 := finite_quotient_span_of_birational hB ha
    have h2 : IsNoetherian A (B ⧸ Ideal.span {algebraMap A B a}) := inferInstance
    have h3 : IsNoetherian B (B ⧸ Ideal.span {algebraMap A B a}) := isNoetherian_of_tower A h2
    refine Submodule.fg_of_fg_map_of_fg_inf_ker (Submodule.mkQ (Ideal.span {algebraMap A B a}))
      (IsNoetherian.noetherian _) ?_
    rw [Submodule.ker_mkQ, inf_eq_right.mpr ((Ideal.span_singleton_le_iff_mem _).mpr haI)]
    exact Submodule.fg_span_singleton _
  · refine ⟨fun {p} hp hp' => ?_⟩
    obtain ⟨a, ha, hap⟩ := key p hp
    have h1 := finite_quotient_span_of_birational hB ha
    have h2 : Module.Finite A (B ⧸ p) :=
      Module.Finite.of_surjective (Ideal.Quotient.factorₐ A
        ((Ideal.span_singleton_le_iff_mem _).mpr hap)).toLinearMap
        (Ideal.Quotient.factor_surjective ((Ideal.span_singleton_le_iff_mem _).mpr hap))
    have h3 : ((⊥ : Ideal (B ⧸ p)).comap (algebraMap A (B ⧸ p))).IsMaximal := by
      refine Ring.DimensionLEOne.maximalOfPrime ?_ inferInstance
      intro h
      have : a ∈ (⊥ : Ideal (B ⧸ p)).comap (algebraMap A (B ⧸ p)) := by
        rw [Ideal.mem_comap, Ideal.mem_bot]
        exact Ideal.Quotient.eq_zero_iff_mem.mpr hap
      rw [h] at this
      exact ha this
    have h4 := Ideal.isMaximal_of_isIntegral_of_isMaximal_comap (R := A) (⊥ : Ideal (B ⧸ p)) h3
    exact Ideal.Quotient.maximal_of_isField _ (Ring.isField_iff_maximal_bot.mpr h4)

end KrullAkizuki

section Existence

variable {L : Type*} [Field L]

theorem exists_discreteValuationSubring_of_subring (B : Subring L) [IsNoetherianRing B]
    (hB : ∀ z : L, ∃ c ∈ B, c ≠ 0 ∧ c * z ∈ B) {y : L} (hy : y ∈ B) (hy0 : y ≠ 0)
    (hy1 : y⁻¹ ∉ B) :
    ∃ V : ValuationSubring L, IsDiscreteValuationRing V ∧ B ≤ V.toSubring ∧ y ∈ V.nonunits := by
  set y' : B := ⟨y, hy⟩ with hy'
  have hyu : ¬ IsUnit y' := by
    intro h
    obtain ⟨z, hz⟩ := h.exists_right_inv
    have hz' : y * (z : L) = 1 := congrArg Subtype.val hz
    apply hy1
    rw [← eq_inv_of_mul_eq_one_right hz']
    exact z.2
  have hspan : Ideal.span {y'} ≠ ⊤ := by
    rwa [Ne, Ideal.span_singleton_eq_top]
  obtain ⟨p, hp⟩ : Nonempty (Ideal.span {y'}).minimalPrimes := Ideal.nonempty_minimalPrimes hspan
  haveI hpp : p.IsPrime := hp.1.1
  have hyp : y' ∈ p := hp.1.2 (Ideal.mem_span_singleton_self y')
  have hht : p.height ≤ 1 := Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes _ p hp
  set A0 := (LocalSubring.ofPrime B p).toSubring with hA0
  haveI : IsNoetherianRing A0 := IsLocalization.isNoetherianRing p.primeCompl A0 inferInstance
  haveI : Ring.KrullDimLE 1 A0 := by
    rw [Ring.krullDimLE_iff, IsLocalization.AtPrime.ringKrullDim_eq_height p A0]
    exact_mod_cast hht
  haveI : Ring.DimensionLEOne A0 := ⟨fun hq hq' => Ideal.IsPrime.isMaximal_of_ne_bot hq' hq⟩
  set y'' : A0 := algebraMap B A0 y' with hy''
  have hy''m : y'' ∈ IsLocalRing.maximalIdeal A0 := by
    rw [← IsLocalization.AtPrime.map_eq_maximalIdeal p A0]
    exact Ideal.mem_map_of_mem _ hyp
  have hspan2 : Ideal.span {y''} ≠ ⊤ := by
    rw [Ne, Ideal.span_singleton_eq_top]
    exact (IsLocalRing.mem_maximalIdeal _).mp hy''m
  obtain ⟨V, hAV, hVy⟩ := Ideal.image_subset_nonunits_valuationSubring _ hspan2
  have hyV : y ∈ V.nonunits := hVy ⟨y'', Ideal.mem_span_singleton_self _, rfl⟩
  have hBV : B ≤ V.toSubring := (LocalSubring.le_ofPrime B p).trans hAV
  letI : Algebra A0 V := (Subring.inclusion hAV).toAlgebra
  haveI : FaithfulSMul A0 V := (faithfulSMul_iff_algebraMap_injective A0 V).mpr
    fun a b h => Subtype.ext (show (a : L) = b from congrArg (fun v : V => (v : L)) h)
  have hbir : ∀ x : V, ∃ c : A0, c ≠ 0 ∧ ∃ b : A0, algebraMap A0 V c * x = algebraMap A0 V b := by
    intro x
    obtain ⟨c, hc, hc0, hcx⟩ := hB x
    refine ⟨⟨c, LocalSubring.le_ofPrime B p hc⟩, fun h => hc0 (congrArg Subtype.val h),
      ⟨c * x, LocalSubring.le_ofPrime B p hcx⟩, Subtype.ext rfl⟩
  have hKA := krullAkizuki_of_birational (A := A0) (B := V) hbir
  haveI : IsNoetherianRing V := hKA.1
  haveI : IsPrincipalIdealRing V := ((IsBezout.TFAE (R := V)).out 0 1).mp hKA.1
  have hVy0 : y ∈ V := hBV hy
  have hne : IsLocalRing.maximalIdeal V ≠ ⊥ := by
    intro h
    have hm : (⟨y, hVy0⟩ : V) ∈ IsLocalRing.maximalIdeal V :=
      (ValuationSubring.valuation_lt_one_iff V _).mpr ((ValuationSubring.mem_nonunits_iff V).mp hyV)
    rw [h, Ideal.mem_bot] at hm
    exact hy0 (congrArg Subtype.val hm)
  exact ⟨V, IsDiscreteValuationRing.mk hne, hBV, hyV⟩

variable {R : Type*} [CommRing R] [IsNoetherianRing R] [Algebra R L]

theorem exists_discreteValuationSubring_of_valuationSubring [Algebra.EssFiniteType R L]
    (W : ValuationSubring L) (hW : ∀ r, algebraMap R L r ∈ W) {s t : Set L} (hsf : s.Finite)
    (htf : t.Finite) (hs : ∀ x ∈ s, x ∈ W) (ht : ∀ x ∈ t, x ∈ W.nonunits) (h0 : ∃ x ∈ t, x ≠ 0) :
    ∃ V : ValuationSubring L, IsDiscreteValuationRing V ∧ (∀ r, algebraMap R L r ∈ V) ∧
      (∀ x ∈ s, x ∈ V) ∧ ∀ x ∈ t, x ∈ V.nonunits := by
  classical
  obtain ⟨x₀, hx₀, hx₀0⟩ := h0
  obtain ⟨y, hyt, hy⟩ := Set.exists_max_image t W.valuation htf ⟨x₀, hx₀⟩
  have hy0 : y ≠ 0 := by
    rintro rfl
    exact hx₀0 (by simpa using hy x₀ hx₀)
  obtain ⟨σ, hσ⟩ := (Algebra.essFiniteType_iff R L).mp inferInstance
  let g : L → L := fun e => if e ∈ W then e else e⁻¹
  let G : Set L := g '' σ ∪ s ∪ (fun x => x / y) '' t ∪ {y}
  have hG : G.Finite :=
    (((σ.finite_toSet.image _).union hsf).union (htf.image _)).union (Set.finite_singleton _)
  let W' : Subalgebra R L := { W.toSubring with algebraMap_mem' := hW }
  let B := Algebra.adjoin R G
  have hBW : B ≤ W' := by
    refine Algebra.adjoin_le ?_
    rintro x (((⟨e, -, rfl⟩ | hx) | ⟨e, he, rfl⟩) | rfl)
    · change g e ∈ W
      simp only [g]
      split_ifs with h
      · exact h
      · exact (W.mem_or_inv_mem e).resolve_left h
    · exact hs x hx
    · change e / y ∈ W
      rw [← W.valuation_le_one_iff, map_div₀]
      exact div_le_one_of_le₀ (hy e he) zero_le
    · exact W.nonunits_subset (ht _ hyt)
  have hBft : Algebra.FiniteType R B := .adjoin_of_finite hG
  have hBn : IsNoetherianRing B := Algebra.FiniteType.isNoetherianRing R B
  have hBn' : IsNoetherianRing B.toSubring := hBn
  have hyB : y ∈ B := Algebra.subset_adjoin (Or.inr rfl)
  have hfrac : ∀ z : L, ∃ c ∈ B.toSubring, c ≠ 0 ∧ c * z ∈ B.toSubring := by
    let F := Subfield.closure (B : Set L)
    let F' : Subalgebra R L :=
      { F.toSubring with algebraMap_mem' := fun r => Subfield.subset_closure (B.algebraMap_mem r) }
    have h1 : Algebra.adjoin R (σ : Set L) ≤ F' := by
      refine Algebra.adjoin_le fun e he => ?_
      have h2 : g e ∈ F :=
        Subfield.subset_closure (Algebra.subset_adjoin (Or.inl (Or.inl (Or.inl ⟨e, he, rfl⟩))))
      change e ∈ F
      simp only [g] at h2
      split_ifs at h2 with h
      · exact h2
      · simpa using F.inv_mem h2
    intro z
    obtain ⟨u, hu, hu', hzu⟩ := hσ z
    have hz : z ∈ F := by
      have := F.div_mem (h1 hzu) (h1 hu)
      rwa [mul_div_cancel_right₀ _ hu'.ne_zero] at this
    obtain ⟨a, ha, b, hb, rfl⟩ := Subfield.mem_closure_iff.mp hz
    have hc : Subring.closure (B : Set L) = B.toSubring := Subring.closure_eq B.toSubring
    rw [hc] at ha hb
    rcases eq_or_ne b 0 with rfl | hb0
    · exact ⟨1, one_mem _, one_ne_zero, by simp⟩
    · exact ⟨b, hb, hb0, by rwa [mul_div_cancel₀ _ hb0]⟩
  have hy1 : y⁻¹ ∉ B.toSubring := fun h =>
    ((W.mem_nonunits_iff_or.mp (ht y hyt)).resolve_left hy0) (hBW h)
  obtain ⟨V, hV, hBV, hyV⟩ :=
    exists_discreteValuationSubring_of_subring B.toSubring hfrac hyB hy0 hy1
  refine ⟨V, hV, fun r => hBV (B.algebraMap_mem r),
    fun x hx => hBV (Algebra.subset_adjoin (Or.inl (Or.inl (Or.inr hx)))), fun x hx => ?_⟩
  have h1 : x / y ∈ V := hBV (Algebra.subset_adjoin (Or.inl (Or.inr ⟨x, hx, rfl⟩)))
  rw [V.mem_nonunits_iff] at hyV ⊢
  rw [← V.valuation_le_one_iff] at h1
  rw [← div_mul_cancel₀ x hy0, map_mul]
  exact mul_lt_one_of_nonneg_of_lt_one_right h1 zero_le hyV

end Existence

section Domination

variable {R L : Type*} [CommRing R] [IsLocalRing R] [Field L]

theorem localSubring_range_le_valuationSubring_iff (f : R →+* L) (V : ValuationSubring L) :
    LocalSubring.range f ≤ V.toLocalSubring ↔
      (∀ r, f r ∈ V) ∧ ∀ r ∈ maximalIdeal R, f r ∈ V.nonunits := by
  have hl : IsLocalHom f.rangeRestrict := .of_surjective _ f.rangeRestrict_surjective
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨fun r => h1 ⟨r, rfl⟩, fun r hr => ?_⟩
    refine (ValuationSubring.coe_mem_nonunits_iff (a := ⟨f r, h1 ⟨r, rfl⟩⟩)).mpr fun hu => hr ?_
    exact hl.1 r (h2.1 _ hu)
  · rintro ⟨h1, h2⟩
    refine ⟨by rintro _ ⟨r, rfl⟩; exact h1 r, ⟨?_⟩⟩
    rintro ⟨_, r, rfl⟩ hu
    by_contra hn
    have hr : r ∈ maximalIdeal R := fun h => hn (h.map f.rangeRestrict)
    exact (ValuationSubring.coe_mem_nonunits_iff (a := ⟨f r, h1 r⟩)).mp (h2 r hr) hu

theorem localSubring_range_le_valuationSubring_iff_isLocalHom (f : R →+* L)
    (V : ValuationSubring L) :
    LocalSubring.range f ≤ V.toLocalSubring ↔
      ∃ h : ∀ r, f r ∈ V, IsLocalHom (f.codRestrict V h) := by
  rw [localSubring_range_le_valuationSubring_iff]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨h1, ⟨fun r hu => ?_⟩⟩
    by_contra hn
    exact (ValuationSubring.coe_mem_nonunits_iff (a := ⟨f r, h1 r⟩)).mp (h2 r hn) hu
  · rintro ⟨h1, h2⟩
    refine ⟨h1, fun r hr => ?_⟩
    exact (ValuationSubring.coe_mem_nonunits_iff (a := ⟨f r, h1 r⟩)).mpr fun hu => hr (h2.1 r hu)

variable [IsNoetherianRing R] [Algebra R L]

theorem exists_discreteValuationSubring_dominating_of_le [Algebra.EssFiniteType R L]
    (W : ValuationSubring L) (hW : LocalSubring.range (algebraMap R L) ≤ W.toLocalSubring)
    {s t : Set L} (hsf : s.Finite) (htf : t.Finite) (hs : ∀ x ∈ s, x ∈ W)
    (ht : ∀ x ∈ t, x ∈ W.nonunits)
    (h0 : (∃ r ∈ maximalIdeal R, algebraMap R L r ≠ 0) ∨ ∃ x ∈ t, x ≠ 0) :
    ∃ V : ValuationSubring L, IsDiscreteValuationRing V ∧
      LocalSubring.range (algebraMap R L) ≤ V.toLocalSubring ∧
      (∀ x ∈ s, x ∈ V) ∧ ∀ x ∈ t, x ∈ V.nonunits := by
  rw [localSubring_range_le_valuationSubring_iff] at hW
  obtain ⟨g, hg⟩ := (maximalIdeal R).fg_of_isNoetherianRing
  have hgm : ∀ r ∈ g, r ∈ maximalIdeal R := fun r hr => hg ▸ Ideal.subset_span hr
  obtain ⟨V, hV, h1, h2, h3⟩ := exists_discreteValuationSubring_of_valuationSubring W hW.1
    (t := algebraMap R L '' g ∪ t) hsf ((g.finite_toSet.image _).union htf) hs
    (by
      rintro x (⟨r, hr, rfl⟩ | hx)
      · exact hW.2 r (hgm r hr)
      · exact ht x hx)
    (by
      rcases h0 with ⟨r, hr, hr0⟩ | ⟨x, hx, hx0⟩
      · by_contra hn
        apply hr0
        have : maximalIdeal R ≤ RingHom.ker (algebraMap R L) := by
          rw [← hg, Ideal.span_le]
          intro a ha
          by_contra h
          exact hn ⟨_, Or.inl ⟨a, ha, rfl⟩, h⟩
        exact this hr
      · exact ⟨x, Or.inr hx, hx0⟩)
  refine ⟨V, hV, ?_, h2, fun x hx => h3 x (Or.inr hx)⟩
  rw [localSubring_range_le_valuationSubring_iff]
  refine ⟨h1, fun r hr => ?_⟩
  have : maximalIdeal R ≤ (maximalIdeal V).comap ((algebraMap R L).codRestrict V h1) := by
    rw [← hg, Ideal.span_le]
    intro a ha
    exact (ValuationSubring.coe_mem_nonunits_iff (a := ⟨_, h1 a⟩)).mp (h3 _ (Or.inl ⟨a, ha, rfl⟩))
  exact (ValuationSubring.coe_mem_nonunits_iff (a := ⟨_, h1 r⟩)).mpr (this hr)

theorem exists_discreteValuationSubring_dominating_of_essFiniteType [Algebra.EssFiniteType R L]
    [FaithfulSMul R L] (hR : ¬ IsField R) :
    ∃ V : ValuationSubring L, IsDiscreteValuationRing V ∧
      LocalSubring.range (algebraMap R L) ≤ V.toLocalSubring := by
  obtain ⟨W, hW⟩ := (LocalSubring.range (algebraMap R L)).exists_le_valuationSubring
  obtain ⟨r, hr, hr0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot
    (isField_iff_maximalIdeal_eq.not.mp hR)
  obtain ⟨V, h1, h2, -⟩ := exists_discreteValuationSubring_dominating_of_le W hW
    Set.finite_empty Set.finite_empty (by simp) (by simp) (Or.inl ⟨r, hr, by simpa using hr0⟩)
  exact ⟨V, h1, h2⟩

theorem exists_discreteValuationSubring_dominating_notMem [Algebra.EssFiniteType R L] {x : L}
    (hx : ¬ IsIntegral R x) :
    ∃ V : ValuationSubring L, IsDiscreteValuationRing V ∧
      LocalSubring.range (algebraMap R L) ≤ V.toLocalSubring ∧ x ∉ V := by
  have hx0 : x ≠ 0 := by
    rintro rfl
    exact hx isIntegral_zero
  letI := invertibleOfNonzero (inv_ne_zero hx0)
  let B := Algebra.adjoin R {x⁻¹}
  let xinv : B := ⟨x⁻¹, Algebra.subset_adjoin rfl⟩
  have hne : (maximalIdeal R).map (algebraMap R B) ⊔ Ideal.span {xinv} ≠ ⊤ := by
    intro heq
    obtain ⟨p, hp, hpx⟩ := Algebra.exists_aeval_invOf_eq_zero_of_idealMap_adjoin_sup_span_eq_top
      x⁻¹ _ (maximalIdeal.isMaximal R).ne_top heq
    have H : IsUnit p.leadingCoeff := of_not_not fun h ↦ by simpa using sub_mem h hp
    refine hx ⟨Polynomial.C H.unit⁻¹.1 * p,
      Polynomial.monic_C_mul_of_mul_leadingCoeff_eq_one (by simp), ?_⟩
    rw [invOf_eq_inv, inv_inv] at hpx
    rw [← Polynomial.aeval_def, map_mul, hpx, mul_zero]
  obtain ⟨W, hW, hW'⟩ := Ideal.image_subset_nonunits_valuationSubring (A := B.toSubring) _ hne
  have hWd : LocalSubring.range (algebraMap R L) ≤ W.toLocalSubring := by
    rw [localSubring_range_le_valuationSubring_iff]
    exact ⟨fun r => hW (B.algebraMap_mem r), fun r hr =>
      hW' ⟨_, Ideal.mem_sup_left (Ideal.mem_map_of_mem _ hr), rfl⟩⟩
  have hxW : x⁻¹ ∈ W.nonunits := hW' ⟨xinv, Ideal.mem_sup_right (Ideal.subset_span rfl), rfl⟩
  obtain ⟨V, h1, h2, -, h3⟩ := exists_discreteValuationSubring_dominating_of_le W hWd
    Set.finite_empty (Set.finite_singleton x⁻¹) (by simp) (by simpa using hxW)
    (Or.inr ⟨_, rfl, inv_ne_zero hx0⟩)
  exact ⟨V, h1, h2, (V.inv_mem_nonunits_iff.mp (h3 _ rfl)).resolve_left hx0⟩

theorem integralClosure_eq_iInf_discreteValuationSubring [Algebra.EssFiniteType R L] :
    (integralClosure R L).toSubring =
      ⨅ V : {V : ValuationSubring L // IsDiscreteValuationRing V ∧
        LocalSubring.range (algebraMap R L) ≤ V.toLocalSubring}, V.1.toSubring := by
  refine le_antisymm (le_iInf fun V x hx => ?_) fun x hx => ?_
  · have h := ((localSubring_range_le_valuationSubring_iff _ _).mp V.2.2).1
    letI : Algebra R V.1 := ((algebraMap R L).codRestrict V.1 h).toAlgebra
    have : IsScalarTower R V.1 L := .of_algebraMap_eq fun _ => rfl
    obtain ⟨y, rfl⟩ := (IsIntegrallyClosed.isIntegral_iff (R := V.1) (K := L)).mp
      (IsIntegral.tower_top (R := R) hx)
    exact y.2
  · by_contra hn
    obtain ⟨V, h1, h2, h3⟩ := exists_discreteValuationSubring_dominating_notMem (R := R) hn
    exact h3 (iInf_le_of_le (α := Subring L) ⟨V, h1, h2⟩ le_rfl hx)

end Domination

section Completion

theorem isDiscreteValuationRing_of_maximalIdeal_eq_span {S : Type*} [CommRing S] [IsLocalRing S]
    [IsHausdorff (maximalIdeal S) S] {π : S} (hπ : maximalIdeal S = Ideal.span {π})
    (hn : ¬ IsNilpotent π) :
    ∃ _ : IsDomain S, IsDiscreteValuationRing S ∧ Irreducible π := by
  classical
  have key : ∀ x : S, x ≠ 0 → ∃ n : ℕ, Associated (π ^ n) x := by
    intro x hx
    have h1 : ∃ n : ℕ, ¬ π ^ (n + 1) ∣ x := by
      by_contra h
      push Not at h
      refine hx (IsHausdorff.haus' (I := maximalIdeal S) x fun n => ?_)
      rw [SModEq.zero, smul_eq_mul, Ideal.mul_top, hπ, Ideal.span_singleton_pow,
        Ideal.mem_span_singleton]
      exact (pow_dvd_pow π n.le_succ).trans (h n)
    have h2 : π ^ Nat.find h1 ∣ x := by
      rcases Nat.eq_zero_or_eq_succ_pred (Nat.find h1) with h | h
      · simp [h]
      · rw [h]
        exact of_not_not (Nat.find_min h1 (by omega))
    obtain ⟨u, hu⟩ := h2
    have h3 : IsUnit u := by
      by_contra h
      have h4 : u ∈ maximalIdeal S := h
      rw [hπ, Ideal.mem_span_singleton] at h4
      apply Nat.find_spec h1
      rw [pow_succ]
      exact (mul_dvd_mul_left _ h4).trans (dvd_of_eq hu.symm)
    exact ⟨_, h3.unit, hu.symm⟩
  have : NoZeroDivisors S := ⟨fun {x y} hxy => by
    by_contra h
    push Not at h
    obtain ⟨m, hm⟩ := key x h.1
    obtain ⟨n, hn'⟩ := key y h.2
    have := hm.mul_mul hn'
    rw [hxy, associated_zero_iff_eq_zero, ← pow_add] at this
    exact hn ⟨_, this⟩⟩
  have hd : IsDomain S := NoZeroDivisors.to_isDomain S
  have hπ0 : π ≠ 0 := by
    rintro rfl
    exact hn IsNilpotent.zero
  have hirr : Irreducible π :=
    ((Ideal.span_singleton_prime hπ0).mp (hπ ▸ inferInstance)).irreducible
  exact ⟨hd, IsDiscreteValuationRing.ofHasUnitMulPowIrreducibleFactorization
    ⟨π, hirr, fun {x} hx => key x hx⟩, hirr⟩

variable (V : Type*) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]

theorem algebraMap_adicCompletion_injective_of_dvr :
    Function.Injective (algebraMap V (AdicCompletion (maximalIdeal V) V)) :=
  AdicCompletion.of_injective (maximalIdeal V) V

theorem adicCompletion_isDVR_irreducible {π : V} (hπ : Irreducible π) :
    ∃ _ : IsDomain (AdicCompletion (maximalIdeal V) V),
      IsDiscreteValuationRing (AdicCompletion (maximalIdeal V) V) ∧
      Irreducible (algebraMap V (AdicCompletion (maximalIdeal V) V) π) := by
  refine isDiscreteValuationRing_of_maximalIdeal_eq_span ?_ ?_
  · rw [AdicCompletion.maximalIdeal_eq_map]
    conv_lhs => enter [2]; rw [hπ.maximalIdeal_eq]
    rw [Ideal.map_span, Set.image_singleton]
  · rw [IsNilpotent.map_iff (algebraMap_adicCompletion_injective_of_dvr V)]
    exact fun h => hπ.ne_zero h.eq_zero

instance isDomain_adicCompletion_of_dvr : IsDomain (AdicCompletion (maximalIdeal V) V) :=
  (adicCompletion_isDVR_irreducible V (IsDiscreteValuationRing.exists_irreducible V).choose_spec).1

instance isDiscreteValuationRing_adicCompletion_of_dvr :
    IsDiscreteValuationRing (AdicCompletion (maximalIdeal V) V) :=
  (adicCompletion_isDVR_irreducible V (IsDiscreteValuationRing.exists_irreducible V).choose_spec).2.1

variable {V} in

theorem irreducible_algebraMap_adicCompletion_of_dvr {π : V} (hπ : Irreducible π) :
    Irreducible (algebraMap V (AdicCompletion (maximalIdeal V) V) π) :=
  (adicCompletion_isDVR_irreducible V hπ).2.2

end Completion

section KrullAkizukiFinite

variable {A : Type*} [CommRing A] [IsDomain A] [IsNoetherianRing A] [Ring.DimensionLEOne A]
  (K : Type*) {L : Type*} [Field K] [Algebra A K] [IsFractionRing A K] [Field L] [Algebra K L]
  [Algebra A L] [IsScalarTower A K L] [FiniteDimensional K L]

include K in

theorem krullAkizuki (B : Subalgebra A L) : IsNoetherianRing B ∧ Ring.DimensionLEOne B := by
  have hinj : Function.Injective (algebraMap A L) := by
    rw [IsScalarTower.algebraMap_eq A K L]
    exact (algebraMap K L).injective.comp (IsFractionRing.injective A K)
  have : FaithfulSMul A L := (faithfulSMul_iff_algebraMap_injective _ _).mpr hinj
  have halg : Algebra.IsAlgebraic A L :=
    (IsFractionRing.comap_isAlgebraic_iff (A := A) (K := K) (C := L)).mpr inferInstance
  let T : Set L := {x | x ∈ B ∧ IsIntegral A x}
  obtain ⟨s, hsT, hs⟩ := (Submodule.fg_span_iff_fg_span_finset_subset (R := K) T).mp
    (IsNoetherian.noetherian _)
  let C := Algebra.adjoin A (s : Set L)
  have hCB : C ≤ B := Algebra.adjoin_le fun x hx => (hsT hx).1
  have hCf : Module.Finite A C :=
    Algebra.finite_adjoin_of_finite_of_isIntegral s.finite_toSet fun x hx => (hsT hx).2
  have hCn : IsNoetherianRing C := IsNoetherianRing.of_finite A C
  have hCd : Ring.DimensionLEOne C := Ring.DimensionLEOne.of_isIntegral A C
  letI : Algebra C B := (Subalgebra.inclusion hCB).toAlgebra
  have : FaithfulSMul C B := (faithfulSMul_iff_algebraMap_injective _ _).mpr
    (Subalgebra.inclusion_injective hCB)
  refine krullAkizuki_of_birational (A := C) (B := B) fun x => ?_
  obtain ⟨c, hc, hcx⟩ := (halg.1 (x : L)).exists_integral_multiple
  have h1 : c • (x : L) ∈ Submodule.span K (s : Set L) :=
    hs ▸ Submodule.subset_span ⟨B.smul_mem x.2 c, hcx⟩
  obtain ⟨d, hd⟩ := multiple_mem_span_of_mem_localization_span (nonZeroDivisors A) K _ _ h1
  have h2 : (d : A) • c • (x : L) ∈ C := Algebra.span_le_adjoin A _ hd
  refine ⟨algebraMap A C (d * c), ?_, ⟨_, h2⟩, Subtype.ext ?_⟩
  · intro h
    have h3 : algebraMap A L (d * c) = 0 := congrArg Subtype.val h
    exact mul_ne_zero (nonZeroDivisors.coe_ne_zero d) hc (hinj (h3.trans (map_zero _).symm))
  · change algebraMap A L (d * c) * x = (d : A) • c • (x : L)
    rw [← mul_smul, Algebra.smul_def]

include K in

theorem isDedekindDomain_integralClosure_of_dimensionLEOne :
    IsDedekindDomain (integralClosure A L) := by
  obtain ⟨h1, h2⟩ := krullAkizuki K (integralClosure A L)
  have h3 : IsIntegrallyClosed (integralClosure A L) :=
    integralClosure.isIntegrallyClosedOfFiniteExtension K
  have h4 : IsDedekindRing (integralClosure A L) := { }
  exact { }

end KrullAkizukiFinite

section Main

universe u v w

variable (R : Type u) [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsLocalRing R]
  (K : Type v) [Field K] [Algebra R K] [IsFractionRing R K]

theorem exists_discreteValuationSubring_dominating (L : Type w) [Field L] [Algebra K L]
    [Algebra R L] [IsScalarTower R K L] [FiniteDimensional K L] (hR : ¬ IsField R) :
    ∃ V : ValuationSubring L, IsDiscreteValuationRing V ∧
      LocalSubring.range (algebraMap R L) ≤ V.toLocalSubring := by
  have : FaithfulSMul R L := (faithfulSMul_iff_algebraMap_injective _ _).mpr (by
    rw [IsScalarTower.algebraMap_eq R K L]
    exact (algebraMap K L).injective.comp (IsFractionRing.injective R K))
  have : Algebra.EssFiniteType R K := .of_isLocalization K (nonZeroDivisors R)
  have : Algebra.EssFiniteType R L := .comp R K L
  exact exists_discreteValuationSubring_dominating_of_essFiniteType hR

theorem range_algebraMap_eq_iInf_discreteValuationSubring [IsIntegrallyClosed R] :
    (algebraMap R K).range =
      ⨅ V : {V : ValuationSubring K // IsDiscreteValuationRing V ∧
        LocalSubring.range (algebraMap R K) ≤ V.toLocalSubring}, V.1.toSubring := by
  have : Algebra.EssFiniteType R K := .of_isLocalization K (nonZeroDivisors R)
  rw [← integralClosure_eq_iInf_discreteValuationSubring]
  ext x
  exact (IsIntegrallyClosed.isIntegral_iff (R := R) (K := K)).symm

variable {R K} in

theorem exists_algebraMap_eq_of_forall_discreteValuationSubring [IsIntegrallyClosed R] {x : K}
    (hx : ∀ V : ValuationSubring K, IsDiscreteValuationRing V → (∀ r, algebraMap R K r ∈ V) →
      (∀ r ∈ maximalIdeal R, algebraMap R K r ∈ V.nonunits) → x ∈ V) :
    ∃ r : R, algebraMap R K r = x := by
  change x ∈ (algebraMap R K).range
  rw [range_algebraMap_eq_iInf_discreteValuationSubring, Subring.mem_iInf]
  rintro ⟨V, h1, h2⟩
  rw [localSubring_range_le_valuationSubring_iff] at h2
  exact hx V h1 h2.1 h2.2

theorem injective_and_isLocalHom_adicCompletion_comp {S : Type*} [CommRing S] {V : Type*}
    [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (f : S →+* V)
    (hf : Function.Injective f) [IsLocalHom f] :
    Function.Injective ((algebraMap V (AdicCompletion (maximalIdeal V) V)).comp f) ∧
      IsLocalHom ((algebraMap V (AdicCompletion (maximalIdeal V) V)).comp f) :=
  ⟨(algebraMap_adicCompletion_injective_of_dvr V).comp hf, RingHom.isLocalHom_comp _ _⟩

theorem exists_complete_discreteValuationRing_dominating (hR : ¬ IsField R) :
    ∃ (O : Type u) (_ : CommRing O) (_ : IsDomain O) (_ : IsDiscreteValuationRing O)
      (_ : IsAdicComplete (maximalIdeal O) O) (φ : R →+* O),
      Function.Injective φ ∧ IsLocalHom φ := by
  obtain ⟨V, hV, h⟩ :=
    exists_discreteValuationSubring_dominating R (FractionRing R) (FractionRing R) hR
  obtain ⟨h1, h2⟩ := (localSubring_range_le_valuationSubring_iff_isLocalHom _ _).mp h
  exact ⟨AdicCompletion (maximalIdeal V) V, inferInstance, inferInstance, inferInstance,
    inferInstance, _, injective_and_isLocalHom_adicCompletion_comp
      ((algebraMap R (FractionRing R)).codRestrict V h1)
      fun a b hab => IsFractionRing.injective R (FractionRing R) (congrArg Subtype.val hab)⟩

theorem map_maximalIdeal_pow_le {S O : Type*} [CommRing S] [IsLocalRing S] [CommRing O]
    [IsLocalRing O] (φ : S →+* O) [IsLocalHom φ] (n : ℕ) :
    (maximalIdeal S ^ n).map φ ≤ maximalIdeal O ^ n := by
  rw [Ideal.map_pow]
  exact Ideal.pow_right_mono (map_maximalIdeal_le φ) n

open TensorProduct in

theorem tensorProduct_mk_one_injective_of_isTorsionFree {S : Type*} [CommRing S] [IsDomain S]
    (F : Type*) [Field F] [Algebra S F] [FaithfulSMul S F] (M : Type*) [AddCommGroup M]
    [Module S M] [Module.IsTorsionFree S M] :
    Function.Injective (TensorProduct.mk S F M 1) := by
  letI : Algebra (FractionRing S) F := FractionRing.liftAlgebra S F
  have h1 : Function.Injective (TensorProduct.mk S (FractionRing S) M 1) := by
    rw [IsLocalizedModule.injective_iff_isRegular (nonZeroDivisors S)]
    intro c
    exact IsSMulRegular.of_ne_zero (nonZeroDivisors.coe_ne_zero c)
  have h2 := Module.FaithfullyFlat.tensorProduct_mk_injective
    (A := FractionRing S) (B := F) (FractionRing S ⊗[S] M)
  have h3 := (AlgebraTensorModule.cancelBaseChange S (FractionRing S) F F M).injective.comp
    (h2.comp h1)
  intro a b hab
  apply h3
  simpa using hab

theorem exists_complete_discreteValuationRing_ker_eq {S : Type u} [CommRing S]
    [IsNoetherianRing S] [IsLocalRing S] (q : Ideal S) [q.IsPrime] (hq : q ≠ maximalIdeal S) :
    ∃ (O : Type u) (_ : CommRing O) (_ : IsDomain O) (_ : IsDiscreteValuationRing O)
      (_ : IsAdicComplete (maximalIdeal O) O) (φ : S →+* O),
      RingHom.ker φ = q ∧ IsLocalHom φ := by
  have hl : IsLocalRing (S ⧸ q) := .of_surjective' _ Ideal.Quotient.mk_surjective
  have hm : IsLocalHom (Ideal.Quotient.mk q) := .of_surjective _ Ideal.Quotient.mk_surjective
  have hf : ¬ IsField (S ⧸ q) := fun h =>
    hq (eq_maximalIdeal (Ideal.Quotient.maximal_of_isField q h))
  obtain ⟨O, _, _, _, _, φ, h1, h2⟩ := exists_complete_discreteValuationRing_dominating (S ⧸ q) hf
  refine ⟨O, inferInstance, inferInstance, inferInstance, inferInstance,
    φ.comp (Ideal.Quotient.mk q), ?_, RingHom.isLocalHom_comp _ _⟩
  rw [RingHom.ker_comp_of_injective _ h1, Ideal.mk_ker]

theorem exists_complete_discreteValuationRing_of_prime_lt {A : Type u} [CommRing A]
    [IsNoetherianRing A] (q p : Ideal A) [q.IsPrime] [p.IsPrime] (hqp : q < p) :
    ∃ (O : Type u) (_ : CommRing O) (_ : IsDomain O) (_ : IsDiscreteValuationRing O)
      (_ : IsAdicComplete (maximalIdeal O) O) (φ : A →+* O),
      RingHom.ker φ = q ∧ (maximalIdeal O).comap φ = p := by
  let S := Localization.AtPrime p
  have hdis : Disjoint (p.primeCompl : Set A) q := by
    rw [Set.disjoint_left]
    exact fun x hx hx' => hx (hqp.le hx')
  have hq' : (q.map (algebraMap A S)).IsPrime :=
    IsLocalization.isPrime_of_isPrime_disjoint p.primeCompl S q inferInstance hdis
  have hc : (q.map (algebraMap A S)).comap (algebraMap A S) = q :=
    IsLocalization.comap_map_of_isPrime_disjoint p.primeCompl S inferInstance hdis
  have hm : (maximalIdeal S).comap (algebraMap A S) = p :=
    Localization.AtPrime.comap_maximalIdeal
  obtain ⟨O, _, _, _, _, φ, h1, h2⟩ := exists_complete_discreteValuationRing_ker_eq
    (q.map (algebraMap A S)) (fun h => hqp.ne (by rw [← hc, h, hm]))
  refine ⟨O, inferInstance, inferInstance, inferInstance, inferInstance,
    φ.comp (algebraMap A S), ?_, ?_⟩
  · rw [← RingHom.comap_ker, h1, hc]
  · rw [← Ideal.comap_comap, maximalIdeal_comap, hm]

open AlgebraicGeometry CategoryTheory in

theorem exists_complete_discreteValuationRing_of_specializes {X : Scheme.{u}}
    [IsLocallyNoetherian X] {η x : X} (h : η ⤳ x) (hne : η ≠ x) :
    ∃ (O : CommRingCat.{u}) (_ : IsDomain O) (_ : IsDiscreteValuationRing O)
      (_ : IsAdicComplete (maximalIdeal O) O) (f : Spec O ⟶ X),
      f (⊥ : PrimeSpectrum O) = η ∧ f (closedPoint O) = x := by
  have h1 : η ∈ Set.range (X.fromSpecStalk x) := by
    rw [Scheme.range_fromSpecStalk]
    exact h
  obtain ⟨q, rfl⟩ := h1
  have hq : q.asIdeal ≠ maximalIdeal (X.presheaf.stalk x) := by
    intro e
    apply hne
    have : q = closedPoint (X.presheaf.stalk x) := PrimeSpectrum.ext e
    rw [this, Scheme.fromSpecStalk_closedPoint]
  have hqp : Ideal.IsPrime (α := X.presheaf.stalk x) q.asIdeal := q.isPrime
  obtain ⟨O, _, hO, hO', hO'', φ, h1, h2⟩ :=
    exists_complete_discreteValuationRing_ker_eq (S := X.presheaf.stalk x) q.asIdeal hq
  refine ⟨.of O, hO, hO', hO'', Spec.map (CommRingCat.ofHom φ) ≫ X.fromSpecStalk x, ?_, ?_⟩
  · refine (Scheme.Hom.comp_apply _ _ _).trans (congrArg (X.fromSpecStalk x) ?_)
    exact PrimeSpectrum.ext h1
  · refine (Scheme.Hom.comp_apply _ _ _).trans
      (Eq.trans (congrArg (X.fromSpecStalk x) ?_) (Scheme.fromSpecStalk_closedPoint (x := x)))
    exact comap_closedPoint φ

theorem discreteValuationRing_dominating_noetherian_local (L : Type w) [Field L] [Algebra K L]
    [Algebra R L] [IsScalarTower R K L] [FiniteDimensional K L] :
    (¬ IsField R → ∃ V : ValuationSubring L, IsDiscreteValuationRing V ∧
      LocalSubring.range (algebraMap R L) ≤ V.toLocalSubring) ∧
    (IsIntegrallyClosed R → (algebraMap R K).range =
      ⨅ V : {V : ValuationSubring K // IsDiscreteValuationRing V ∧
        LocalSubring.range (algebraMap R K) ≤ V.toLocalSubring}, V.1.toSubring) ∧
    ∀ (V : ValuationSubring L) [IsDiscreteValuationRing V],
      LocalSubring.range (algebraMap R L) ≤ V.toLocalSubring →
      IsDiscreteValuationRing (AdicCompletion (maximalIdeal V) V) ∧
      IsAdicComplete (maximalIdeal (AdicCompletion (maximalIdeal V) V))
        (AdicCompletion (maximalIdeal V) V) ∧
      (∀ π : V, Irreducible π → Irreducible (algebraMap V (AdicCompletion (maximalIdeal V) V) π)) ∧
      ∃ h : ∀ r, algebraMap R L r ∈ V,
        Function.Injective ((algebraMap V (AdicCompletion (maximalIdeal V) V)).comp
          ((algebraMap R L).codRestrict V h)) ∧
        IsLocalHom ((algebraMap V (AdicCompletion (maximalIdeal V) V)).comp
          ((algebraMap R L).codRestrict V h)) := by
  refine ⟨exists_discreteValuationSubring_dominating R K L,
    fun _ => range_algebraMap_eq_iInf_discreteValuationSubring R K, fun V _ h => ?_⟩
  obtain ⟨h1, h2⟩ := (localSubring_range_le_valuationSubring_iff_isLocalHom _ _).mp h
  have hinj : Function.Injective (algebraMap R L) := by
    rw [IsScalarTower.algebraMap_eq R K L]
    exact (algebraMap K L).injective.comp (IsFractionRing.injective R K)
  exact ⟨inferInstance, inferInstance, fun π => irreducible_algebraMap_adicCompletion_of_dvr, h1,
    injective_and_isLocalHom_adicCompletion_comp _
      fun a b hab => hinj (congrArg Subtype.val hab)⟩

end Main

end GlobalTheory
