import Mathlib
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsRationalUnitaryDeterminantMapRationalUnitaryTo
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnitOpenAndCongrOpen
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsProdUnifMulUnitIdl
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnderEqIffConjPl

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.FrobeniusOrbits Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.L2.Host GlobalTheory.Mem.Chr

namespace GlobalTheory.Mem.Col2

variable {R : Ranks} (H : Formalism.BasicNotions.Host R) (SQ : Finset (HeightOneSpectrum (𝓞 H.E)))

def AtQ (v : HeightOneSpectrum (𝓞 H.E)) : Prop := v ∈ SQ ∨ ∃ w ∈ SQ, IsConjPl H w v

def congQ : Set (Ideles H.E) :=
  {a | a ∈ unitIdl H.E ∧ (∀ k v, OverP H (H.g k) v → Valued.v ((a : AdeleRing (𝓞 H.E) H.E).2 v - 1) < 1) ∧
    ∀ v, AtQ H SQ v → Valued.v ((a : AdeleRing (𝓞 H.E) H.E).2 v - 1) < 1}

def KDq : Subgroup (Ideles H.E) :=
  Subgroup.closure (congQ H SQ ∪ {a | ∃ v k, a = locF H.F v k})

abbrev DtQ : Type := Ideles H.E ⧸ KDq H SQ

open Classical in

def tildeQ (χ : HChar H.E) : DtQ H SQ →* ℂˣ :=
  if h : KDq H SQ ≤ (χ.1.comp (finPartI H.E)).ker then QuotientGroup.lift (KDq H SQ) (χ.1.comp (finPartI H.E)) h else 1

def muTilQ (mu : Fin R.m → HChar H.E) (j : ℕ) : DtQ H SQ →* ℂˣ :=
  if h : 1 ≤ j ∧ j ≤ R.m then tildeQ H SQ (mu ⟨j - 1, by omega⟩) else 1

def UOQ : Subgroup (DtQ H SQ) := (unitIdl H.E).map (QuotientGroup.mk' (KDq H SQ))

def IsUnitaryPointsMapFinerDeterminants (f : (letI := H.cmStar; unitary H.E) →* DtQ H SQ) : Prop :=
  letI := H.cmStar
  ∀ (k : H.Eˣ) (z : unitary H.E), (z : H.E) * H.conj (k : H.E) = k → QuotientGroup.mk (diagUnits H.E k) = f z

open Classical in

def e1Q : (letI := H.cmStar; unitary H.E) →* DtQ H SQ := if h : ∃ f, IsUnitaryPointsMapFinerDeterminants H SQ f then h.choose else 1

def relDetQ (N : ℕ) (M M' : Submodule (𝓞 H.E) (Fin N → H.E)) : DtQ H SQ ⧸ UOQ H SQ :=
  QuotientGroup.mk (QuotientGroup.mk (∏ᶠ w : HeightOneSpectrum (𝓞 H.E),
    localIdele H.E w (atFin w (unif w)) ^ (ordSub w (detSub M') - ordSub w (detSub M)).toNat))

theorem congQ_subset_congG : congQ H SQ ⊆ congG H := fun _ h => ⟨h.1, h.2.1⟩

theorem mem_KDq_of_congQ {a : Ideles H.E} (h : a ∈ congQ H SQ) : a ∈ KDq H SQ :=
  Subgroup.subset_closure (Or.inl h)

theorem locF_mem_KDq (v : HeightOneSpectrum (𝓞 H.F)) (k : (H.F)ˣ) : locF H.F v k ∈ KDq H SQ :=
  Subgroup.subset_closure (Or.inr ⟨v, k, rfl⟩)

theorem KDq_le_iff {B : Subgroup (Ideles H.E)} :
    KDq H SQ ≤ B ↔ (∀ a ∈ congQ H SQ, a ∈ B) ∧ ∀ v k, locF H.F v k ∈ B := by
  refine ⟨fun h => ⟨fun a ha => h (mem_KDq_of_congQ H SQ ha), fun v k => h (locF_mem_KDq H SQ v k)⟩, fun h => ?_⟩
  refine (Subgroup.closure_le _).2 ?_
  rintro a (ha | ⟨v, k, rfl⟩)
  exacts [h.1 a ha, h.2 v k]

theorem KDq_le_KD : KDq H SQ ≤ KD H :=
  Subgroup.closure_mono (Set.union_subset_union_left _ (congQ_subset_congG H SQ))

theorem KDq_anti {SQ SQ' : Finset (HeightOneSpectrum (𝓞 H.E))} (h : SQ ⊆ SQ') : KDq H SQ' ≤ KDq H SQ :=
  Subgroup.closure_mono (Set.union_subset_union_left _ fun _ ha => ⟨ha.1, ha.2.1, fun v hv =>
    ha.2.2 v (hv.imp (fun h' => h h') fun ⟨w, hw, hc⟩ => ⟨w, h hw, hc⟩)⟩)

theorem congQ_empty : congQ H ∅ = congG H :=
  Set.Subset.antisymm (congQ_subset_congG H ∅) fun _ h => ⟨h.1, h.2, fun v hv => by simp [AtQ] at hv⟩

theorem KDq_empty : KDq H ∅ = KD H := by
  unfold KDq KD
  rw [congQ_empty]

theorem KD_le_sup : KD H ≤ KDq H SQ ⊔ unitIdl H.E := by
  refine (Subgroup.closure_le _).2 ?_
  rintro a (ha | ⟨v, k, rfl⟩)
  · exact Subgroup.mem_sup_right ha.1
  · exact Subgroup.mem_sup_left (locF_mem_KDq H SQ v k)

theorem KDq_sup_unitIdl : KDq H SQ ⊔ unitIdl H.E = KD H ⊔ unitIdl H.E :=
  le_antisymm (sup_le_sup_right (KDq_le_KD H SQ) _) (sup_le (KD_le_sup H SQ) le_sup_right)

theorem finite_level : {v : HeightOneSpectrum (𝓞 H.E) | (∃ k, OverP H (H.g k) v) ∨ AtQ H SQ v}.Finite := by
  have h1 : ∀ k, {v : HeightOneSpectrum (𝓞 H.E) | OverP H (H.g k) v}.Finite := fun k => by
    have h0 : Ideal.span {((H.g k : ℕ) : 𝓞 H.E)} ≠ 0 := by
      rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
      exact Nat.cast_ne_zero.2 (H.g_prime k).ne_zero
    refine (Ideal.finite_factors h0).subset fun v hv => ?_
    exact Ideal.dvd_span_singleton.2 hv
  have h2 : ∀ w, {v : HeightOneSpectrum (𝓞 H.E) | IsConjPl H w v}.Finite := fun w =>
    Set.Subsingleton.finite fun v hv v' hv' => (existsUnique_conjPl H.conj.toRingEquiv w).unique
      ((conjPl_iff_mem _ _ _).2 hv) ((conjPl_iff_mem _ _ _).2 hv')
  refine (((Set.finite_iUnion h1).union SQ.finite_toSet).union (SQ.finite_toSet.biUnion fun w _ => h2 w)).subset ?_
  rintro v (⟨k, hk⟩ | hv | ⟨w, hw, hc⟩)
  · exact Or.inl (Or.inl (Set.mem_iUnion.2 ⟨k, hk⟩))
  · exact Or.inl (Or.inr hv)
  · exact Or.inr (Set.mem_biUnion hw hc)

theorem mem_congQ_of_eq_one {a : Ideles H.E} (hu : a ∈ unitIdl H.E)
    (h : ∀ v, (∃ k, OverP H (H.g k) v) ∨ AtQ H SQ v → (a : AdeleRing (𝓞 H.E) H.E).2 v = 1) : a ∈ congQ H SQ :=
  ⟨hu, fun k v hv => by rw [h v (Or.inl ⟨k, hv⟩), sub_self, map_zero]; exact zero_lt_one,
    fun v hv => by rw [h v (Or.inr hv), sub_self, map_zero]; exact zero_lt_one⟩

theorem infIdele_mem_KDq (w : InfinitePlace H.E) (y : (w.Completion)ˣ) : infIdele H.E w y ∈ KDq H SQ :=
  mem_KDq_of_congQ H SQ (mem_congQ_of_eq_one H SQ (fun v => show Valued.v (1 : v.adicCompletion H.E) = 1 from map_one _)
    fun _ _ => rfl)

theorem isOpen_KDq : IsOpen (KDq H SQ : Set (Ideles H.E)) := by
  have ho := (GlobalTheory.Mem.UnitOpen.unit_open_and_congr_open H.E).2 (finite_level H SQ).toFinset 1
  have hlt : WithZero.exp (-((1 : ℕ) : ℤ)) < (1 : WithZero (Multiplicative ℤ)) := by
    rw [← WithZero.exp_zero, WithZero.exp_lt_exp]; norm_num
  refine Subgroup.isOpen_of_mem_nhds _ (g := 1) (Filter.mem_of_superset (ho.mem_nhds ⟨one_mem _, fun v _ => ?_⟩) ?_)
  · show Valued.v ((1 : v.adicCompletion H.E) - 1) ≤ _
    rw [sub_self, map_zero]
    exact zero_le
  · intro a ha
    refine mem_KDq_of_congQ H SQ ⟨ha.1, fun k v hv => (ha.2 v ?_).trans_lt hlt, fun v hv => (ha.2 v ?_).trans_lt hlt⟩
    · exact (Set.Finite.mem_toFinset _).2 (Or.inl ⟨k, hv⟩)
    · exact (Set.Finite.mem_toFinset _).2 (Or.inr hv)

section Components

variable {L : Type} [Field L] [NumberField L]

def compAt (w : HeightOneSpectrum (𝓞 L)) : Ideles L →* w.adicCompletion L where
  toFun a := (a : AdeleRing (𝓞 L) L).2 w
  map_one' := rfl
  map_mul' _ _ := rfl

theorem compAt_localIdele_self (v : HeightOneSpectrum (𝓞 L)) (x : (v.adicCompletion L)ˣ) :
    compAt v (localIdele L v x) = x := by
  classical
  have := Function.update_self (β := fun w : HeightOneSpectrum (𝓞 L) => w.adicCompletion L) v
    (x : v.adicCompletion L) (fun _ => 1)
  convert this
  rfl

theorem compAt_localIdele_ne {v w : HeightOneSpectrum (𝓞 L)} (hw : w ≠ v) (x : (v.adicCompletion L)ˣ) :
    compAt w (localIdele L v x) = 1 := by
  classical
  have := Function.update_of_ne (β := fun w : HeightOneSpectrum (𝓞 L) => w.adicCompletion L) hw
    (x : v.adicCompletion L) (fun _ => 1)
  convert this
  rfl

variable (F : Type) [Field F] [NumberField F] [Algebra F L]

open Classical in

theorem compAt_locF (w : HeightOneSpectrum (𝓞 L)) (v : HeightOneSpectrum (𝓞 F)) (k : Fˣ) :
    compAt w (locF F v k) = if w.under (𝓞 F) = v then compAt w (diagUnits L (upF F k)) else 1 := by
  unfold locF
  rw [map_prod]
  split_ifs with h
  · rw [Finset.prod_eq_single_of_mem w (show w ∈ aboveF F v from (finite_aboveF F v).mem_toFinset.2 h)
      (fun Q _ hQ => compAt_localIdele_ne hQ.symm _), compAt_localIdele_self]
    rfl
  · refine Finset.prod_eq_one fun Q hQ => compAt_localIdele_ne ?_ _
    rintro rfl
    exact h ((finite_aboveF F v).mem_toFinset.1 hQ)

theorem exists_diag_upF_eq (k : Fˣ) {T : Set (HeightOneSpectrum (𝓞 L))} (hT : T.Finite) :
    ∃ (S : Finset (HeightOneSpectrum (𝓞 F))) (u : Ideles L), u ∈ unitIdl L ∧ (∀ w ∈ T, compAt w u = 1) ∧
      diagUnits L (upF F k) = (∏ v ∈ S, locF F v k) * u := by
  classical
  set d := diagUnits L (upF F k) with hd
  have hfin := hT.union (IdlFact.finite_valAt_ne_one d)
  set S := hfin.toFinset.image fun w => w.under (𝓞 F) with hS
  set P := ∏ v ∈ S, locF (L := L) F v k with hP
  have hc : ∀ w, compAt w P = if w.under (𝓞 F) ∈ S then compAt w d else 1 := fun w => by
    rw [hP, map_prod, Finset.prod_congr rfl fun v _ => compAt_locF F w v k, Finset.prod_ite_eq]
  have h1 : ∀ w, w.under (𝓞 F) ∈ S → compAt w (P⁻¹ * d) = 1 := fun w hw => by
    have e : compAt w d = compAt w P := by rw [hc, if_pos hw]
    rw [map_mul, e, ← map_mul, inv_mul_cancel, map_one]
  have hmem : ∀ w, w ∈ T ∪ {v | IdlFact.valAt v d ≠ 1} → w.under (𝓞 F) ∈ S := fun w hw =>
    Finset.mem_image_of_mem _ (hfin.mem_toFinset.2 hw)
  refine ⟨S, P⁻¹ * d, fun w => ?_, fun w hw => h1 w (hmem w (Or.inl hw)), (mul_inv_cancel_left _ _).symm⟩
  show Valued.v (compAt w (P⁻¹ * d)) = 1
  by_cases hw : w.under (𝓞 F) ∈ S
  · rw [h1 w hw, map_one]
  · have e : compAt w (P⁻¹ * d) = compAt w d := by
      have e' : compAt w P = 1 := by rw [hc, if_neg hw]
      rw [← one_mul (compAt w _), ← e', ← map_mul, mul_inv_cancel_left]
    rw [e]
    by_contra hne
    exact hw (hmem w (Or.inr hne))

end Components

theorem diag_upF_mem_KDq (k : (H.F)ˣ) : diagUnits H.E (upF H.F k) ∈ KDq H SQ := by
  obtain ⟨S, u, hu, h1, e⟩ := exists_diag_upF_eq (L := H.E) H.F k (finite_level H SQ)
  rw [e]
  exact mul_mem (prod_mem fun v _ => locF_mem_KDq H SQ v k) (mem_KDq_of_congQ H SQ (mem_congQ_of_eq_one H SQ hu h1))

def toDtT : DtQ H SQ →* DtT H :=
  QuotientGroup.map (KDq H SQ) (KD H) (MonoidHom.id _) (KDq_le_KD H SQ)

@[simp] theorem toDtT_mk (a : Ideles H.E) : toDtT H SQ (QuotientGroup.mk a) = QuotientGroup.mk a := rfl

theorem toDtT_surjective : Function.Surjective (toDtT H SQ) := fun x => by
  obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective x
  exact ⟨QuotientGroup.mk a, rfl⟩

theorem mk_mem_UOQ {a : Ideles H.E} : (QuotientGroup.mk a : DtQ H SQ) ∈ UOQ H SQ ↔ a ∈ KDq H SQ ⊔ unitIdl H.E := by
  rw [← QuotientGroup.comap_map_mk']
  rfl

theorem comap_UOT : (UOT H).comap (toDtT H SQ) = UOQ H SQ := by
  ext x
  obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective x
  rw [mk_mem_UOQ, KDq_sup_unitIdl, ← QuotientGroup.comap_map_mk']
  rfl

def toDtTMod : DtQ H SQ ⧸ UOQ H SQ →* DtT H ⧸ UOT H :=
  QuotientGroup.map (UOQ H SQ) (UOT H) (toDtT H SQ) (comap_UOT H SQ).ge

@[simp] theorem toDtTMod_mk (x : DtQ H SQ) :
    toDtTMod H SQ (QuotientGroup.mk x) = QuotientGroup.mk (toDtT H SQ x) := rfl

theorem toDtTMod_bijective : Function.Bijective (toDtTMod H SQ) := by
  refine ⟨(injective_iff_map_eq_one _).2 fun x hx => ?_, fun y => ?_⟩
  · obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective x
    rw [toDtTMod_mk, QuotientGroup.eq_one_iff, ← Subgroup.mem_comap, comap_UOT] at hx
    exact (QuotientGroup.eq_one_iff _).2 hx
  · obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective y
    obtain ⟨a, rfl⟩ := toDtT_surjective H SQ b
    exact ⟨QuotientGroup.mk a, rfl⟩

def modEquiv : DtQ H SQ ⧸ UOQ H SQ ≃* DtT H ⧸ UOT H := MulEquiv.ofBijective _ (toDtTMod_bijective H SQ)

theorem toDtTMod_relDetQ (N : ℕ) (M M' : Submodule (𝓞 H.E) (Fin N → H.E)) :
    toDtTMod H SQ (relDetQ H SQ N M M') = relDetT H N M M' := rfl

theorem relDetQ_self (N : ℕ) (M : Submodule (𝓞 H.E) (Fin N → H.E)) : relDetQ H SQ N M M = 1 :=
  (toDtTMod_bijective H SQ).1 (by rw [toDtTMod_relDetQ, relDetT_self, map_one])

theorem tildeQ_mk {χ : HChar H.E} (h : KDq H SQ ≤ (χ.1.comp (finPartI H.E)).ker) (a : Ideles H.E) :
    tildeQ H SQ χ (QuotientGroup.mk a) = χ.1 (finPartI H.E a) := by
  unfold tildeQ
  rw [dif_pos h]
  rfl

theorem tildeQ_eq_comp {χ : HChar H.E} (h : KD H ≤ (χ.1.comp (finPartI H.E)).ker) :
    tildeQ H SQ χ = (tildeD H χ).comp (toDtT H SQ) := by
  refine MonoidHom.ext fun x => ?_
  obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective x
  rw [tildeQ_mk H SQ ((KDq_le_KD H SQ).trans h), MonoidHom.comp_apply, toDtT_mk, tildeD_mk H h]

@[simp] theorem tildeQ_one : tildeQ H SQ 1 = 1 := by
  refine MonoidHom.ext fun x => ?_
  obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective x
  rw [tildeQ_mk H SQ (χ := 1) fun _ _ => rfl]
  rfl

theorem tildeQ_mul {χ χ' : HChar H.E} (h : KDq H SQ ≤ (χ.1.comp (finPartI H.E)).ker)
    (h' : KDq H SQ ≤ (χ'.1.comp (finPartI H.E)).ker) : tildeQ H SQ (χ * χ') = tildeQ H SQ χ * tildeQ H SQ χ' := by
  have h'' : KDq H SQ ≤ ((χ * χ').1.comp (finPartI H.E)).ker := fun a ha => by
    have e : χ.1 (finPartI H.E a) = 1 := h ha
    have e' : χ'.1 (finPartI H.E a) = 1 := h' ha
    show χ.1 (finPartI H.E a) * χ'.1 (finPartI H.E a) = 1
    rw [e, e', one_mul]
  refine MonoidHom.ext fun x => ?_
  obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective x
  rw [MonoidHom.mul_apply, tildeQ_mk H SQ h'', tildeQ_mk H SQ h, tildeQ_mk H SQ h']
  rfl

theorem norm_tildeQ {χ : HChar H.E} (hu : χ.IsUnitary) (x : DtQ H SQ) : ‖((tildeQ H SQ χ x : ℂˣ) : ℂ)‖ = 1 := by
  by_cases h : KDq H SQ ≤ (χ.1.comp (finPartI H.E)).ker
  · obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective x
    rw [tildeQ_mk H SQ h]
    exact hu _
  · unfold tildeQ
    rw [dif_neg h]
    simp

theorem muTilQ_succ (mu : Fin R.m → HChar H.E) (j : Fin R.m) : muTilQ H SQ mu (j.1 + 1) = tildeQ H SQ (mu j) := by
  unfold muTilQ
  rw [dif_pos ⟨Nat.le_add_left 1 j.1, j.2⟩]
  rfl

theorem exists_eq_div_conj : letI := H.cmStar
    ∀ z : unitary H.E, ∃ k : (H.E)ˣ, (z : H.E) * H.conj (k : H.E) = k := by
  letI := H.cmStar
  intro z
  have hcm : IsCMField H.E := H.isCMField_hostE
  have hc : ∀ x, IsCMField.complexConj H.E x = H.conj x := fun x => bridge_star_holds R H x
  have hz : (z : H.E) * H.conj (z : H.E) = 1 := by
    rw [← bridge_star_holds R H]
    exact z.2.2
  by_cases h : 1 + (z : H.E) = 0
  · obtain ⟨x, hx⟩ : ∃ x : H.E, H.conj x ≠ x := by
      by_contra hall
      refine IsCMField.complexConj_ne_one H.E (AlgEquiv.ext fun x => ?_)
      rw [hc]
      exact not_not.1 fun h' => hall ⟨x, h'⟩
    have hcc : H.conj (H.conj x) = x := by
      rw [← hc, ← hc]
      exact IsCMField.complexConj_apply_apply H.E x
    refine ⟨Units.mk0 (H.conj x - x) (sub_ne_zero.2 hx), ?_⟩
    rw [Units.val_mk0, map_sub, hcc]
    linear_combination (x - H.conj x) * h
  · refine ⟨Units.mk0 _ h, ?_⟩
    rw [Units.val_mk0, map_add, map_one]
    linear_combination hz

theorem mk_diag_eq {z : H.E} {k k' : (H.E)ˣ} (h : z * H.conj (k : H.E) = k) (h' : z * H.conj (k' : H.E) = k') :
    (QuotientGroup.mk (diagUnits H.E k) : DtQ H SQ) = QuotientGroup.mk (diagUnits H.E k') := by
  have hcm : IsCMField H.E := H.isCMField_hostE
  have hc : ∀ x, IsCMField.complexConj H.E x = H.conj x := fun x => bridge_star_holds R H x
  have hk : H.conj (k : H.E) ≠ 0 := (map_ne_zero _).2 k.ne_zero
  have hk0 : (k : H.E) ≠ 0 := k.ne_zero
  have hfix : IsCMField.complexConj H.E ((k⁻¹ * k' : (H.E)ˣ) : H.E) = ((k⁻¹ * k' : (H.E)ˣ) : H.E) := by
    rw [hc, Units.val_mul, Units.val_inv_eq_inv_val, map_mul, map_inv₀]
    field_simp
    linear_combination H.conj (k : H.E) * h' - H.conj (k' : H.E) * h
  have hF : ((k⁻¹ * k' : (H.E)ˣ) : H.E) ∈ H.F := (IsCMField.complexConj_eq_self_iff H.E _).1 hfix
  have h0 : (⟨_, hF⟩ : H.F) ≠ 0 := fun e => (k⁻¹ * k').ne_zero (congrArg Subtype.val e)
  have e : upF (L := H.E) H.F (Units.mk0 _ h0) = k⁻¹ * k' := Units.ext rfl
  rw [QuotientGroup.eq, ← map_inv, ← map_mul, ← e]
  exact diag_upF_mem_KDq H SQ _

theorem exists_isUnitaryPointsMapFinerDeterminants : ∃ f, IsUnitaryPointsMapFinerDeterminants H SQ f := by
  letI := H.cmStar
  choose κ hκ using exists_eq_div_conj H
  refine ⟨MonoidHom.mk' (fun z => QuotientGroup.mk (diagUnits H.E (κ z))) fun z z' => ?_,
    fun k z hk => mk_diag_eq H SQ hk (hκ z)⟩
  rw [← QuotientGroup.mk_mul, ← map_mul]
  refine mk_diag_eq H SQ (hκ (z * z')) ?_
  rw [Units.val_mul, map_mul, Submonoid.coe_mul]
  linear_combination ((z' : H.E) * H.conj (κ z' : H.E)) * hκ z + (κ z : H.E) * hκ z'

theorem isUnitaryPointsMap_unitaryRationalPointsFiner : IsUnitaryPointsMapFinerDeterminants H SQ (e1Q H SQ) := by
  unfold e1Q
  rw [dif_pos (exists_isUnitaryPointsMapFinerDeterminants H SQ)]
  exact (exists_isUnitaryPointsMapFinerDeterminants H SQ).choose_spec

theorem isRationalUnitaryDeterminantMap_rationalUnitary : IsRationalUnitaryDeterminantMap H (e1T H) :=
  isRationalUnitaryDeterminantMap_rationalUnitaryToDeterminants H ⟨(toDtT H ∅).comp (e1Q H ∅), fun k z hk => congrArg (toDtT H ∅) (isUnitaryPointsMap_unitaryRationalPointsFiner H ∅ k z hk)⟩

theorem toDtT_e1Q : letI := H.cmStar
    ∀ z : unitary H.E, toDtT H SQ (e1Q H SQ z) = e1T H z := by
  intro z
  obtain ⟨k, hk⟩ := exists_eq_div_conj H z
  rw [← isUnitaryPointsMap_unitaryRationalPointsFiner H SQ k z hk, toDtT_mk, isRationalUnitaryDeterminantMap_rationalUnitary H k z hk]

example (v : HeightOneSpectrum (𝓞 H.E)) (hv : v ∈ SQ) (x : (v.adicCompletion H.E)ˣ)
    (hx : Valued.v ((x : v.adicCompletion H.E) - 1) = 1) : localIdele H.E v x ∉ congQ H SQ := fun h => by
  have h1 : Valued.v (compAt v (localIdele H.E v x) - 1) < 1 := h.2.2 v (Or.inl hv)
  rw [compAt_localIdele_self, hx] at h1
  exact lt_irrefl _ h1

example (χ : HChar H.E) (h : KDq H SQ ≤ (χ.1.comp (finPartI H.E)).ker) : letI := H.cmStar
    ∀ (k : (H.E)ˣ) (z : unitary H.E), (z : H.E) * H.conj (k : H.E) = k →
      tildeQ H SQ χ (e1Q H SQ z) = χ.1 (finPartI H.E (diagUnits H.E k)) := by
  intro k z hk
  rw [← isUnitaryPointsMap_unitaryRationalPointsFiner H SQ k z hk, tildeQ_mk H SQ h]

example (mu : Fin R.m → HChar H.E) : muTilQ H SQ mu 0 = 1 := by
  unfold muTilQ
  rw [dif_neg (by omega)]

end GlobalTheory.Mem.Col2
