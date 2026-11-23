import Mathlib
import GroundTheory.GlobalFields.SUnits
import GroundTheory.GlobalFields.KummerTheory.Unramified
import GroundTheory.ProfiniteCohomology.RestrictedRamification.IsUnramifiedOutsideIffLeMaxUnramifiedOutside
import GroundTheory.ProfiniteCohomology.RestrictedRamification.SUnitsDefs
import GroundTheory.ProfiniteCohomology.GaloisCohomology.Kummer
set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum CategoryTheory

universe u

section Valuation

theorem valuation_le_one_of_isIntegral {R L : Type*} [CommRing R] [Field L] [Algebra R L]
    (w : Valuation L (WithZero (Multiplicative ℤ))) (hR : ∀ r : R, w (algebraMap R L r) ≤ 1)
    {x : L} (hx : IsIntegral R x) : w x ≤ 1 := by
  let f : R →+* w.integer := (algebraMap R L).codRestrict w.integer hR
  have hx' : IsIntegral w.integer (RingHom.id L x) :=
    IsIntegral.map_of_comp_eq f (RingHom.id L) (by ext r; rfl) hx
  exact (Valuation.integer.integers w).mem_of_integral hx'

theorem exists_mul_pow_le_one {a b : WithZero (Multiplicative ℤ)} (ha0 : a ≠ 0) (ha : a < 1)
    (hb : b ≠ 0) : ∃ N : ℕ, b * a ^ N ≤ 1 := by
  obtain ⟨k, rfl⟩ : ∃ k, a = WithZero.exp k := ⟨_, (WithZero.exp_log ha0).symm⟩
  obtain ⟨m, rfl⟩ : ∃ m, b = WithZero.exp m := ⟨_, (WithZero.exp_log hb).symm⟩
  have hk : k < 0 := by
    rw [← WithZero.exp_zero] at ha
    exact WithZero.exp_lt_exp.1 ha
  refine ⟨m.toNat, ?_⟩
  rw [← WithZero.exp_nsmul, ← WithZero.exp_add, ← WithZero.exp_zero, WithZero.exp_le_exp]
  have : (m.toNat : ℤ) * k ≤ -(m.toNat : ℤ) := by nlinarith [Int.self_le_toNat m]
  rw [nsmul_eq_mul]
  omega

end Valuation

section Compare

variable {F : Type u} [Field F] [NumberField F] {L : Type u} [Field L] [NumberField L] [Algebra F L]
variable (S : Set (HeightOneSpectrum (𝓞 F)))

def underPlace (w : HeightOneSpectrum (𝓞 L)) : HeightOneSpectrum (𝓞 F) :=
  ⟨w.asIdeal.under (𝓞 F), inferInstance, Ideal.under_ne_bot (𝓞 F) w.ne_bot⟩

instance liesOver_underPlace (w : HeightOneSpectrum (𝓞 L)) :
    w.asIdeal.LiesOver (underPlace (F := F) w).asIdeal :=
  ⟨rfl⟩

omit [NumberField F] [NumberField L] in
theorem liesOver_iff_eq_underPlace {w : HeightOneSpectrum (𝓞 L)} {v : HeightOneSpectrum (𝓞 F)} :
    w.asIdeal.LiesOver v.asIdeal ↔ v = underPlace w :=
  ⟨fun h => HeightOneSpectrum.ext h.over, fun h => h ▸ ⟨rfl⟩⟩

variable {S} in
omit [NumberField F] [NumberField L] in
theorem mem_placesOver_iff {w : HeightOneSpectrum (𝓞 L)} :
    w ∈ placesOver S ↔ underPlace w ∈ S := by
  constructor
  · rintro ⟨v, hv, hwv⟩
    rwa [← liesOver_iff_eq_underPlace.1 hwv]
  · intro h
    exact ⟨_, h, inferInstance⟩

theorem valuation_algebraMap_integer_le_one {w : HeightOneSpectrum (𝓞 L)} (hw : w ∉ placesOver S)
    (r : S.integer F) : w.valuation L (algebraMap F L r) ≤ 1 := by
  have hv : underPlace (F := F) w ∉ S := fun h => hw (mem_placesOver_iff.2 h)
  rw [← valuation_liesOver (K := F) L (underPlace (F := F) w) w]
  exact pow_le_one₀ zero_le (r.2 _ hv)

theorem valuation_le_one_of_isIntegral_integer {x : L} (hx : IsIntegral (S.integer F) x)
    {w : HeightOneSpectrum (𝓞 L)} (hw : w ∉ placesOver S) : w.valuation L x ≤ 1 :=
  valuation_le_one_of_isIntegral (w.valuation L)
    (fun r => valuation_algebraMap_integer_le_one S hw r) hx

theorem isIntegral_integer_of_valuation_le_one {x : L}
    (h : ∀ w ∉ placesOver (L := L) S, w.valuation L x ≤ 1) : IsIntegral (S.integer F) x := by
  classical
  rcases eq_or_ne x 0 with rfl | hx0
  · exact isIntegral_zero
  have hT : (Support (𝓞 L) x).Finite := Support.finite (𝓞 L) x
  have hTS : ∀ w ∈ Support (𝓞 L) x, underPlace (F := F) w ∈ S := fun w hw => by
    by_contra hn
    exact (not_lt.2 (h w fun hm => hn (mem_placesOver_iff.1 hm))) hw
  let V : Finset (HeightOneSpectrum (𝓞 F)) := hT.toFinset.image underPlace
  let π : HeightOneSpectrum (𝓞 F) → 𝓞 F := fun v =>
    (Global.SUnit.exists_pow_classNumber_eq_span v).choose
  let t : Fˣ := ∏ v ∈ V, Global.SUnit.placeUnit v
  have htS : t ∈ S.unit F := Subgroup.prod_mem _ fun v hv => by
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.1 hv
    exact Global.SUnit.placeUnit_mem S (hTS w (hT.mem_toFinset.1 hw))
  have ht₀ : (t : F) = algebraMap (𝓞 F) F (∏ v ∈ V, π v) := by
    simp only [t, Units.coe_prod, map_prod]
    rfl
  have hπ : ∀ v, π v ∈ v.asIdeal := fun v => by
    have h1 : π v ∈ Ideal.span {π v} := Ideal.mem_span_singleton_self _
    rw [← (Global.SUnit.exists_pow_classNumber_eq_span v).choose_spec.2] at h1
    exact Ideal.pow_le_self Fintype.card_ne_zero h1
  have hwt : ∀ w ∈ Support (𝓞 L) x, w.valuation L (algebraMap F L t) < 1 := by
    intro w hw
    have hv : underPlace w ∈ V := Finset.mem_image_of_mem _ (hT.mem_toFinset.2 hw)
    have hmem : ∏ v ∈ V, π v ∈ (underPlace (F := F) w).asIdeal := by
      rw [← Finset.mul_prod_erase V π hv]
      exact Ideal.mul_mem_right _ _ (hπ _)
    have hmem' : algebraMap (𝓞 F) (𝓞 L) (∏ v ∈ V, π v) ∈ w.asIdeal := hmem
    rw [ht₀, ← IsScalarTower.algebraMap_apply (𝓞 F) F L,
      IsScalarTower.algebraMap_apply (𝓞 F) (𝓞 L) L, valuation_of_algebraMap]
    exact (intValuation_lt_one_iff_mem w _).2 hmem'
  have hwt1 : ∀ w : HeightOneSpectrum (𝓞 L), w.valuation L (algebraMap F L t) ≤ 1 := by
    intro w
    rw [ht₀, ← IsScalarTower.algebraMap_apply (𝓞 F) F L,
      IsScalarTower.algebraMap_apply (𝓞 F) (𝓞 L) L]
    exact w.valuation_le_one _
  have ht0 : algebraMap F L t ≠ 0 := (map_ne_zero _).2 t.ne_zero
  have hN : ∀ w : HeightOneSpectrum (𝓞 L), ∃ N : ℕ, w ∈ Support (𝓞 L) x →
      w.valuation L x * w.valuation L (algebraMap F L t) ^ N ≤ 1 := by
    intro w
    by_cases hw : w ∈ Support (𝓞 L) x
    · obtain ⟨N, hN⟩ := exists_mul_pow_le_one ((map_ne_zero (w.valuation L)).2 ht0) (hwt w hw)
        ((map_ne_zero (w.valuation L)).2 hx0)
      exact ⟨N, fun _ => hN⟩
    · exact ⟨0, fun h => absurd h hw⟩
  choose Nw hNw using hN
  let N := ∑ w ∈ hT.toFinset, Nw w
  let y := algebraMap F L t ^ N * x
  have hy : ∀ w : HeightOneSpectrum (𝓞 L), w.valuation L y ≤ 1 := by
    intro w
    simp only [y, map_mul, map_pow]
    by_cases hw : w ∈ Support (𝓞 L) x
    · have hle : Nw w ≤ N := Finset.single_le_sum (fun _ _ => Nat.zero_le _)
        (hT.mem_toFinset.2 hw)
      rw [mul_comm]
      exact (mul_le_mul' le_rfl (pow_le_pow_right_of_le_one' (hwt1 w) hle)).trans
        (hNw w hw)
    · have hx1 : w.valuation L x ≤ 1 := not_lt.1 hw
      exact mul_le_one' (pow_le_one₀ zero_le (hwt1 w)) hx1
  obtain ⟨b, hb⟩ := mem_integers_of_valuation_le_one (R := 𝓞 L) L y hy
  have hyI : IsIntegral (S.integer F) y := by
    rw [← hb]
    exact (RingOfIntegers.isIntegral_coe b).tower_top
  have hc : (((t⁻¹ ^ N : Fˣ)) : F) ∈ S.integer F := fun v hv =>
    (Subgroup.pow_mem _ (inv_mem htS) N v hv).le
  have hxy : x = algebraMap (S.integer F) L ⟨_, hc⟩ * y := by
    change x = algebraMap F L (((t⁻¹ ^ N : Fˣ)) : F) * (algebraMap F L t ^ N * x)
    rw [← mul_assoc, ← map_pow, ← map_mul, ← Units.val_pow_eq_pow_val, ← Units.val_mul,
      inv_pow, inv_mul_cancel, Units.val_one, map_one, one_mul]
  rw [hxy]
  exact isIntegral_algebraMap.mul hyI

theorem mem_sUnitsOf_iff_mem_unit {x : Lˣ} :
    x ∈ sUnitsOf S L ↔ x ∈ (placesOver S : Set (HeightOneSpectrum (𝓞 L))).unit L := by
  constructor
  · intro hx w hw
    have h1 := valuation_le_one_of_isIntegral_integer S hx.1 hw
    have h2 := valuation_le_one_of_isIntegral_integer S hx.2 hw
    refine eq_one_of_one_le_mul_left h1 h2 (Eq.ge ?_)
    rw [← map_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, map_one]
  · intro hx
    exact ⟨isIntegral_integer_of_valuation_le_one S fun w hw =>
        (hx w hw).le,
      isIntegral_integer_of_valuation_le_one S fun w hw =>
        (inv_mem hx w hw).le⟩

end Compare

section Invariants

variable {F : Type u} [Field F] [NumberField F] (S : Set (HeightOneSpectrum (𝓞 F)))
variable (E : Type u) [Field E] [Algebra F E]

theorem isIntegral_algebraMap_of_mem_integer {c : F} (hc : c ∈ S.integer F) :
    IsIntegral (S.integer F) (algebraMap F E c) :=
  isIntegral_algebraMap (x := (⟨c, hc⟩ : S.integer F))

theorem isIntegral_of_isIntegral_algebraMap {c : F}
    (hc : IsIntegral (S.integer F) (algebraMap F E c)) : IsIntegral (S.integer F) c :=
  (isIntegral_algHom_iff ((Algebra.ofId F E).restrictScalars (S.integer F))
    (algebraMap F E).injective).1 hc

theorem mem_integer_of_isIntegral {c : F} (hc : IsIntegral (S.integer F) c) : c ∈ S.integer F :=
  fun v _ => valuation_le_one_of_isIntegral (v.valuation F) (fun r => r.2 v ‹_›) hc

variable {E} in

theorem map_mem_sUnitsOf_iff {a : Fˣ} :
    Units.map (algebraMap F E : F →* E) a ∈ sUnitsOf S E ↔ a ∈ S.unit F := by
  constructor
  · intro h v hv
    have h1 : (a : F) ∈ S.integer F :=
      mem_integer_of_isIntegral S (isIntegral_of_isIntegral_algebraMap S E h.1)
    have h2 : ((a⁻¹ : Fˣ) : F) ∈ S.integer F := by
      refine mem_integer_of_isIntegral S (isIntegral_of_isIntegral_algebraMap S E ?_)
      have := h.2
      rwa [← map_inv] at this
    refine eq_one_of_one_le_mul_left (h1 v hv) (h2 v hv) (Eq.ge ?_)
    rw [← map_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, map_one]
  · intro h
    refine ⟨isIntegral_algebraMap_of_mem_integer S E fun v hv => (h v hv).le, ?_⟩
    rw [← map_inv]
    exact isIntegral_algebraMap_of_mem_integer S E fun v hv => (inv_mem h v hv).le

def sUnitsToInvariants : Additive (S.unit F) →+ (galSUnits S E).ρ.invariants where
  toFun a := ⟨Additive.ofMul ⟨Units.map (algebraMap F E : F →* E) (Additive.toMul a : S.unit F),
      (map_mem_sUnitsOf_iff S).2 (Additive.toMul a).2⟩, fun σ =>
    Additive.toMul.injective (Subtype.ext (Units.ext (σ.commutes _)))⟩
  map_zero' := Subtype.ext (Additive.toMul.injective (Subtype.ext (Units.ext (map_one _))))
  map_add' _ _ := Subtype.ext (Additive.toMul.injective (Subtype.ext (Units.ext (map_mul _ _ _))))

@[simp]
theorem coe_sUnitsToInvariants_apply (a : Additive (S.unit F)) :
    (((Additive.toMul (α := sUnitsOf S E) (sUnitsToInvariants S E a).1 : sUnitsOf S E) : Eˣ) : E) =
      algebraMap F E ((Additive.toMul a : S.unit F) : Fˣ) :=
  rfl

theorem sUnitsToInvariants_injective : Function.Injective (sUnitsToInvariants S E) := by
  intro a b h
  apply Additive.toMul.injective
  apply Subtype.ext
  apply Units.ext
  exact (algebraMap F E).injective (congrArg (fun v : (galSUnits S E).ρ.invariants =>
    (((Additive.toMul (α := sUnitsOf S E) v.1 : sUnitsOf S E) : Eˣ) : E)) h)

theorem sUnitsToInvariants_surjective [IsGalois F E] :
    Function.Surjective (sUnitsToInvariants S E) := by
  intro v
  let u : Eˣ := ((Additive.toMul (α := sUnitsOf S E) v.1 : sUnitsOf S E) : Eˣ)
  obtain ⟨a, ha⟩ := (InfiniteGalois.mem_range_algebraMap_iff_fixed (u : E)).2 fun σ =>
    congrArg (fun w : Additive (sUnitsOf S E) =>
      (((Additive.toMul w : sUnitsOf S E) : Eˣ) : E)) (v.2 σ)
  have ha0 : a ≠ 0 := by
    rintro rfl
    rw [map_zero] at ha
    exact u.ne_zero ha.symm
  have hmap : Units.map (algebraMap F E : F →* E) (Units.mk0 a ha0) = u := Units.ext ha
  have hS : Units.mk0 a ha0 ∈ S.unit F := by
    rw [← map_mem_sUnitsOf_iff S (E := E), hmap]
    exact (Additive.toMul (α := sUnitsOf S E) v.1).2
  exact ⟨Additive.ofMul ⟨Units.mk0 a ha0, hS⟩,
    Subtype.ext (Additive.toMul.injective (Subtype.ext hmap))⟩

noncomputable def sUnitsInvariantsEquiv [IsGalois F E] :
    Additive (S.unit F) ≃+ (galSUnits S E).ρ.invariants :=
  AddEquiv.ofBijective (sUnitsToInvariants S E)
    ⟨sUnitsToInvariants_injective S E, sUnitsToInvariants_surjective S E⟩

@[simp]
theorem sUnitsInvariantsEquiv_apply [IsGalois F E] (a : Additive (S.unit F)) :
    sUnitsInvariantsEquiv S E a = sUnitsToInvariants S E a :=
  rfl

noncomputable def h0SUnitsEquiv [IsGalois F E] :
    cohomology (galSUnits S E) 0 ≃+ Additive (S.unit F) :=
  (H0Iso (galSUnits S E)).toLinearEquiv.toAddEquiv.trans (sUnitsInvariantsEquiv S E).symm

end Invariants

section Max

variable (F : Type u) [Field F] [NumberField F] (Ω : Type u) [Field Ω] [Algebra F Ω]
variable (S : Set (HeightOneSpectrum (𝓞 F)))

theorem map_inclusion_mem_sUnitsMax_iff {L : IntermediateField F Ω}
    (hL : L ≤ maxUnramifiedOutside F Ω S) {x : Lˣ} :
    Units.map (IntermediateField.inclusion hL : L →* maxUnramifiedOutside F Ω S) x ∈
      sUnitsMax F Ω S ↔ x ∈ sUnitsOf S L := by
  let f := (IntermediateField.inclusion hL).restrictScalars (S.integer F)
  have hf : Function.Injective f := (IntermediateField.inclusion hL).toRingHom.injective
  constructor
  · intro h
    refine ⟨(isIntegral_algHom_iff f hf).1 h.1, (isIntegral_algHom_iff f hf).1 ?_⟩
    have := h.2
    rwa [← map_inv] at this
  · intro h
    refine ⟨(isIntegral_algHom_iff f hf).2 h.1, ?_⟩
    rw [← map_inv]
    exact (isIntegral_algHom_iff f hf).2 h.2

variable [IsGalois F Ω]

theorem exists_of_mem_sUnitsMax {y : (maxUnramifiedOutside F Ω S)ˣ}
    (hy : y ∈ sUnitsMax F Ω S) :
    ∃ (L : IntermediateField F Ω) (_ : FiniteDimensional F L)
      (hL : L ≤ maxUnramifiedOutside F Ω S) (x : Lˣ), x ∈ sUnitsOf S L ∧
        Units.map (IntermediateField.inclusion hL : L →* maxUnramifiedOutside F Ω S) x = y := by
  obtain ⟨L, hf, hu, hmem⟩ :=
    (mem_maxUnramifiedOutside_iff S).1 (y : maxUnramifiedOutside F Ω S).2
  have hL := le_maxUnramifiedOutside S hu
  have hx0 : (⟨_, hmem⟩ : L) ≠ 0 := by
    intro h
    apply y.ne_zero
    apply Subtype.ext
    have := congrArg Subtype.val h
    simp at this
  have hmap : Units.map (IntermediateField.inclusion hL : L →* maxUnramifiedOutside F Ω S)
      (Units.mk0 _ hx0) = y := Units.ext rfl
  refine ⟨L, hf, hL, Units.mk0 _ hx0, ?_, hmap⟩
  rw [← map_inclusion_mem_sUnitsMax_iff F Ω S hL, hmap]
  exact hy

end Max

section Roots

variable {F : Type u} [Field F] [NumberField F] {Ω : Type u} [Field Ω] [Algebra F Ω]
variable (S : Set (HeightOneSpectrum (𝓞 F)))

theorem adjoin_gen_eq_top (L : Type u) [Field L] [Algebra L Ω] (α : Ω) :
    IntermediateField.adjoin L {IntermediateField.AdjoinSimple.gen L α} = ⊤ := by
  apply IntermediateField.map_injective (IntermediateField.adjoin L {α}).val
  rw [IntermediateField.adjoin_map, Set.image_singleton, IntermediateField.val_mk,
    IntermediateField.AdjoinSimple.coe_gen, ← AlgHom.fieldRange_eq_map,
    IntermediateField.fieldRange_val]

variable [IsGalois F Ω]

theorem mem_maxUnramifiedOutside_of_pow_eq {n : ℕ} (hn : n ≠ 0)
    (hnS : ∀ v ∉ S, ((n : ℕ) : 𝓞 F) ∉ v.asIdeal) {y : (maxUnramifiedOutside F Ω S)ˣ}
    (hy : y ∈ sUnitsMax F Ω S) {α : Ω} (hα : α ^ n = ((y : maxUnramifiedOutside F Ω S) : Ω)) :
    α ∈ maxUnramifiedOutside F Ω S := by
  obtain ⟨L, hfin, hLle, x, hxS, rfl⟩ := exists_of_mem_sUnitsMax F Ω S hy
  have : NumberField L := NumberField.of_module_finite F L
  have hxU := (mem_sUnitsOf_iff_mem_unit S).1 hxS
  have hLu : IsUnramifiedOutside S L := (isUnramifiedOutside_iff_le_maxUnramifiedOutside S).2 hLle
  have hα' : α ^ n = algebraMap L Ω (x : L) := hα
  have hαint : IsIntegral L α := by
    refine IsIntegral.of_pow (Nat.pos_of_ne_zero hn) ?_
    rw [hα']
    exact isIntegral_algebraMap
  let M : IntermediateField L Ω := IntermediateField.adjoin L {α}
  have : FiniteDimensional L M := IntermediateField.adjoin.finiteDimensional hαint
  have : NumberField M := NumberField.of_module_finite L M
  have hgen : α ^ n = algebraMap L Ω (x : L) := hα'
  have hβ : IntermediateField.AdjoinSimple.gen L α ^ n = algebraMap L M (x : L) := by
    apply Subtype.ext
    rw [SubmonoidClass.coe_pow, IntermediateField.AdjoinSimple.coe_gen, hgen]
    rfl
  have hMu : IsUnramifiedOutside (placesOver S) M := by
    intro w hw
    refine Global.Kummer.isUnramifiedIn_of_pow_eq x hβ (adjoin_gen_eq_top L α) w ?_ ?_
    · intro hmem
      have hv : underPlace (F := F) w ∉ S := fun h => hw (mem_placesOver_iff.2 h)
      apply hnS _ hv
      change ((n : ℕ) : 𝓞 F) ∈ Ideal.comap (algebraMap (𝓞 F) (𝓞 L)) w.asIdeal
      rw [Ideal.mem_comap, map_natCast]
      exact hmem
    · rw [hxU w hw, WithZero.log_one]
      exact dvd_zero _
  have hMF := (isUnramifiedOutside_restrictScalars_iff S hLu M).2 hMu
  have : FiniteDimensional F (M.restrictScalars F) := FiniteDimensional.trans F L M
  exact le_maxUnramifiedOutside S hMF (IntermediateField.mem_adjoin_simple_self L α)

theorem mem_maxUnramifiedOutside_of_pow_eq_one {n : ℕ} (hn : n ≠ 0)
    (hnS : ∀ v ∉ S, ((n : ℕ) : 𝓞 F) ∉ v.asIdeal) {ζ : Ω} (hζ : ζ ^ n = 1) :
    ζ ∈ maxUnramifiedOutside F Ω S :=
  mem_maxUnramifiedOutside_of_pow_eq S hn hnS (sUnitsMax F Ω S).one_mem hζ

theorem mem_sUnitsOf_of_pow_mem (E : Type u) [Field E] [Algebra F E] {n : ℕ} (hn : n ≠ 0)
    {β : Eˣ} (hβ : β ^ n ∈ sUnitsOf S E) : β ∈ sUnitsOf S E := by
  refine ⟨IsIntegral.of_pow (Nat.pos_of_ne_zero hn) ?_, IsIntegral.of_pow (Nat.pos_of_ne_zero hn) ?_⟩
  · rw [← Units.val_pow_eq_pow_val]
    exact hβ.1
  · rw [← Units.val_pow_eq_pow_val, inv_pow]
    exact hβ.2

variable [IsSepClosed Ω]

theorem exists_pow_eq_of_mem_sUnitsMax {n : ℕ} (hn : n ≠ 0)
    (hnS : ∀ v ∉ S, ((n : ℕ) : 𝓞 F) ∉ v.asIdeal) {y : (maxUnramifiedOutside F Ω S)ˣ}
    (hy : y ∈ sUnitsMax F Ω S) : ∃ β ∈ sUnitsMax F Ω S, β ^ n = y := by
  have : NeZero ((n : ℕ) : Ω) := ⟨by
    rw [← map_natCast (algebraMap F Ω)]
    exact (map_ne_zero _).2 (Nat.cast_ne_zero.2 hn)⟩
  obtain ⟨α, hα⟩ := IsSepClosed.exists_pow_nat_eq
    (((y : maxUnramifiedOutside F Ω S) : Ω)) n
  have hαS := mem_maxUnramifiedOutside_of_pow_eq S hn hnS hy hα
  have hα0 : (⟨α, hαS⟩ : maxUnramifiedOutside F Ω S) ≠ 0 := by
    intro h
    have h' : α = 0 := congrArg Subtype.val h
    rw [h', zero_pow hn] at hα
    exact y.ne_zero (Subtype.ext hα.symm)
  have hpow : Units.mk0 _ hα0 ^ n = y := Units.ext (Subtype.ext (by
    rw [Units.val_pow_eq_pow_val, Units.val_mk0, SubmonoidClass.coe_pow]
    exact hα))
  refine ⟨Units.mk0 _ hα0, mem_sUnitsOf_of_pow_mem S _ hn (hpow ▸ hy), hpow⟩

theorem sUnitsKummerSequence_shortExact (n : ℕ) [NeZero n]
    (hnS : ∀ v ∉ S, ((n : ℕ) : 𝓞 F) ∉ v.asIdeal) :
    (sUnitsKummerSequence S (maxUnramifiedOutside F Ω S) n).ShortExact where
  exact := by
    apply shortComplex_exact_of_forall_exists
    intro x hx
    let x' : Additive (sUnitsMax F Ω S) := x
    have hx2 : n • x' = 0 :=
      (nsmul_id_hom_apply (galSUnits S (maxUnramifiedOutside F Ω S)) n x).symm.trans hx
    have hx' : (Additive.toMul x' : sUnitsMax F Ω S) ^ n = 1 := by
      rw [← toMul_nsmul, hx2]
      rfl
    have hmem : ((Additive.toMul x' : sUnitsMax F Ω S) : (maxUnramifiedOutside F Ω S)ˣ) ∈
        rootsOfUnity n (maxUnramifiedOutside F Ω S) := by
      rw [mem_rootsOfUnity, ← Subgroup.coe_pow, hx']
      rfl
    exact ⟨Additive.ofMul ⟨_, hmem⟩, rfl⟩
  mono_f := (Rep.mono_iff_injective _).2 fun a b h =>
    Additive.toMul.injective (Subtype.ext (congrArg
      (fun z : Additive (sUnitsMax F Ω S) => ((Additive.toMul z : sUnitsMax F Ω S) :
        (maxUnramifiedOutside F Ω S)ˣ)) h))
  epi_g := (Rep.epi_iff_surjective _).2 fun y => by
    obtain ⟨β, hβ, hβn⟩ := exists_pow_eq_of_mem_sUnitsMax S (NeZero.ne n) hnS
      (Additive.toMul y : sUnitsMax F Ω S).2
    refine ⟨Additive.ofMul ⟨β, hβ⟩, ?_⟩
    refine (nsmul_id_hom_apply (galSUnits S (maxUnramifiedOutside F Ω S)) n _).trans ?_
    apply Additive.toMul.injective
    apply Subtype.ext
    change β ^ n = _
    exact hβn

end Roots

end GroundTheory.ProfCoh
