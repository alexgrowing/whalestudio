import Mathlib

open MeasureTheory Set Topology Filter
open scoped Pointwise ENNReal

namespace GlobalTheory

structure IsAEAddOrbitSection (G : Type*) {X : Type*} [VAdd G X] [MeasurableSpace X]
    (D : Set X) (μ : Measure X) : Prop where
  protected nullMeasurableSet : NullMeasurableSet D μ
  protected ae_covers : ∀ᵐ x ∂μ, ∃ g : G, g +ᵥ x ∈ D
  protected ae_unique : ∀ᵐ x ∂μ, x ∈ D → ∀ g : G, g +ᵥ x ∈ D → g +ᵥ x = x

@[to_additive IsAEAddOrbitSection]
structure IsAEOrbitSection (G : Type*) {X : Type*} [SMul G X] [MeasurableSpace X]
    (D : Set X) (μ : Measure X) : Prop where
  protected nullMeasurableSet : NullMeasurableSet D μ
  protected ae_covers : ∀ᵐ x ∂μ, ∃ g : G, g • x ∈ D
  protected ae_unique : ∀ᵐ x ∂μ, x ∈ D → ∀ g : G, g • x ∈ D → g • x = x

theorem isAEOrbitSection_sign_Ici : IsAEOrbitSection ℤˣ (Ici (0 : ℝ)) volume where
  nullMeasurableSet := measurableSet_Ici.nullMeasurableSet
  ae_covers := Eventually.of_forall fun x => by
    rcases le_total 0 x with h | h
    · exact ⟨1, by simpa using h⟩
    · exact ⟨-1, by simpa using h⟩
  ae_unique := Eventually.of_forall fun x hx g hg => by
    rcases Int.units_eq_one_or g with rfl | rfl
    · simp
    · have h1 : x ≤ 0 := by simpa using hg
      have : x = 0 := le_antisymm h1 hx
      simp [this]

theorem isAEAddOrbitSection_zmultiples_Ico :
    IsAEAddOrbitSection (AddSubgroup.zmultiples (1 : ℝ)) (Ico (0 : ℝ) 1) volume where
  nullMeasurableSet := measurableSet_Ico.nullMeasurableSet
  ae_covers := Eventually.of_forall fun x =>
    ⟨⟨(-⌊x⌋) • (1 : ℝ), AddSubgroup.zsmul_mem_zmultiples _ _⟩, by
      have h1 := Int.floor_le x
      have h2 := Int.lt_floor_add_one x
      simp only [AddSubgroup.mk_vadd, vadd_eq_add, mem_Ico, zsmul_eq_mul, Int.cast_neg]
      constructor <;> linarith⟩
  ae_unique := Eventually.of_forall fun x hx g hg => by
    obtain ⟨g, n, rfl⟩ := g
    simp only [AddSubgroup.mk_vadd, vadd_eq_add, mem_Ico, zsmul_eq_mul, mul_one] at hg hx ⊢
    have h1 : (n : ℝ) < 1 := by linarith [hg.2, hx.1]
    have h2 : (-1 : ℝ) < n := by linarith [hg.1, hx.2]
    have h1' : n < 1 := by exact_mod_cast h1
    have h2' : -1 < n := by exact_mod_cast h2
    have : n = 0 := by omega
    simp [this]

section Existence

variable {G X : Type*} [Group G] [MulAction G X]

@[to_additive exists_measurableSet_addOrbitSection_of_discreteOrbits
]
theorem exists_measurableSet_orbitSection_of_discreteOrbits [Countable G] [TopologicalSpace X]
    [SecondCountableTopology X] [MeasurableSpace X] [OpensMeasurableSpace X]
    [MeasurableConstSMul G X] (hfix : ∀ g : G, MeasurableSet {x : X | g • x = x})
    (hdisc : ∀ x : X, ∃ U ∈ 𝓝 x, ∀ g : G, g • x ∈ U → g • x = x) :
    ∃ D : Set X, MeasurableSet D ∧ (∀ x, ∃ g : G, g • x ∈ D) ∧
      ∀ x ∈ D, ∀ g : G, g • x ∈ D → g • x = x := by
  classical
  obtain ⟨b, hbc, -, hb⟩ := TopologicalSpace.exists_countable_basis X
  obtain ⟨B, hB⟩ := (hbc.insert ∅).exists_eq_range (insert_nonempty _ _)
  have hBo : ∀ n, IsOpen (B n) := fun n => by
    have : B n ∈ insert ∅ b := hB ▸ mem_range_self n
    rcases this with h | h
    · rw [h]; exact isOpen_empty
    · exact hb.isOpen h
  let S : ℕ → Set X := fun n => B n ∩ ⋂ g : G, (((g • ·) ⁻¹' B n)ᶜ ∪ {x | g • x = x})
  have hSm : ∀ n, MeasurableSet (S n) := fun n =>
    (hBo n).measurableSet.inter <| MeasurableSet.iInter fun g =>
      ((measurable_const_smul g) (hBo n).measurableSet).compl.union (hfix g)
  have hSmem : ∀ n x, x ∈ S n ↔ x ∈ B n ∧ ∀ g : G, g • x ∈ B n → g • x = x := fun n x => by
    simp only [S, mem_inter_iff, mem_iInter, mem_union, mem_compl_iff, mem_preimage,
      mem_setOf_eq, imp_iff_not_or]
  have hS : ∀ x, ∃ n, x ∈ S n := fun x => by
    obtain ⟨U, hU, h⟩ := hdisc x
    obtain ⟨t, ht, hxt, htU⟩ := hb.mem_nhds_iff.1 hU
    have : t ∈ range B := hB ▸ mem_insert_of_mem _ ht
    obtain ⟨n, rfl⟩ := this
    exact ⟨n, (hSmem n x).2 ⟨hxt, fun g hg => h g (htU hg)⟩⟩
  let T : ℕ → Set X := fun n => ⋃ g : G, (g • ·) ⁻¹' S n
  have hTm : ∀ n, MeasurableSet (T n) := fun n =>
    MeasurableSet.iUnion fun g => (measurable_const_smul g) (hSm n)
  have hTmem : ∀ n x, x ∈ T n ↔ ∃ g : G, g • x ∈ S n := fun n x => by simp [T]
  refine ⟨⋃ n, S n \ ⋃ m, ⋃ (_ : m < n), T m, ?_, ?_, ?_⟩
  · exact MeasurableSet.iUnion fun n => (hSm n).diff <|
      MeasurableSet.iUnion fun m => MeasurableSet.iUnion fun _ => hTm m
  · intro x
    have hx : ∃ n, x ∈ T n := by
      obtain ⟨n, hn⟩ := hS x
      exact ⟨n, (hTmem n x).2 ⟨1, by simpa using hn⟩⟩
    obtain ⟨g, hg⟩ := (hTmem _ x).1 (Nat.find_spec hx)
    refine ⟨g, mem_iUnion.2 ⟨Nat.find hx, hg, fun h => ?_⟩⟩
    obtain ⟨m, hm, h⟩ := mem_iUnion₂.1 h
    obtain ⟨k, hk⟩ := (hTmem _ _).1 h
    exact Nat.find_min hx hm ((hTmem _ _).2 ⟨k * g, by rwa [mul_smul]⟩)
  · intro x hx g hg
    obtain ⟨n, hn, hn'⟩ := mem_iUnion.1 hx
    obtain ⟨m, hm, hm'⟩ := mem_iUnion.1 hg
    rcases lt_trichotomy m n with h | rfl | h
    · exact (hn' (mem_iUnion₂.2 ⟨m, h, (hTmem _ _).2 ⟨g, hm⟩⟩)).elim
    · exact ((hSmem _ _).1 hn).2 g ((hSmem _ _).1 hm).1
    · exact (hm' (mem_iUnion₂.2 ⟨n, h, (hTmem _ _).2 ⟨g⁻¹, by rwa [inv_smul_smul]⟩⟩)).elim

end Existence

section Comparison

variable {G X : Type*} [Group G] [MulAction G X] [MeasurableSpace X] {μ : Measure X}

@[to_additive measure_le_of_ae_unique_of_ae_covers_add
]
theorem measure_le_of_ae_unique_of_ae_covers [Countable G] [MeasurableConstSMul G X]
    [SMulInvariantMeasure G X μ] {S B : Set X} (hS : NullMeasurableSet S μ)
    (hB : NullMeasurableSet B μ) (hu : ∀ᵐ x ∂μ, x ∈ S → ∀ g : G, g • x ∈ S → g • x = x)
    (hc : ∀ᵐ x ∂μ, x ∈ S → ∃ g : G, g • x ∈ B) : μ S ≤ μ B := by
  classical
  obtain ⟨e, he⟩ := exists_injective_nat G
  have hq : ∀ g : G, Measure.QuasiMeasurePreserving (g • · : X → X) μ μ := fun g =>
    (measurePreserving_smul g μ).quasiMeasurePreserving
  let P : G → Set X := fun g => (S ∩ (g • ·) ⁻¹' B) \ ⋃ h, ⋃ (_ : e h < e g), (h • ·) ⁻¹' B
  have hPm : ∀ g, NullMeasurableSet (P g) μ := fun g =>
    (hS.inter (hB.preimage (hq g))).diff <|
      NullMeasurableSet.iUnion fun h => NullMeasurableSet.iUnion fun _ => hB.preimage (hq h)
  let Q : G → Set X := fun g => (g⁻¹ • ·) ⁻¹' P g
  have hQm : ∀ g, NullMeasurableSet (Q g) μ := fun g => (hPm g).preimage (hq _)
  have h1 : S ≤ᵐ[μ] ⋃ g, P g := by
    filter_upwards [hc] with x hx hxS
    have hex : ∃ n, ∃ g : G, e g = n ∧ g • x ∈ B := by
      obtain ⟨g, hg⟩ := hx hxS
      exact ⟨_, g, rfl, hg⟩
    obtain ⟨g, hg, hgB⟩ := Nat.find_spec hex
    refine mem_iUnion.2 ⟨g, ⟨hxS, hgB⟩, fun h => ?_⟩
    obtain ⟨k, hk, h⟩ := mem_iUnion₂.1 h
    exact Nat.find_min hex (hg ▸ hk) ⟨k, rfl, h⟩
  have h2 : Pairwise (Function.onFun (AEDisjoint μ) Q) := by
    intro g h hgh
    have := (hq g⁻¹).ae hu
    refine measure_mono_null (fun y hy => ?_) this
    intro hy'
    obtain ⟨⟨⟨hg1, hg2⟩, hg3⟩, ⟨hh1, hh2⟩, hh3⟩ := hy
    have key : h⁻¹ • y = g⁻¹ • y := by
      have := hy' hg1 (h⁻¹ * g) (by simpa [mul_smul] using hh1)
      simpa [mul_smul] using this
    rcases lt_trichotomy (e g) (e h) with hl | hl | hl
    · exact hh3 (mem_iUnion₂.2 ⟨g, hl, by rw [mem_preimage]; beta_reduce; rw [key]; exact hg2⟩)
    · exact hgh (he hl)
    · exact hg3 (mem_iUnion₂.2 ⟨h, hl, by rw [mem_preimage]; beta_reduce; rw [← key]; exact hh2⟩)
  calc μ S ≤ μ (⋃ g, P g) := measure_mono_ae h1
    _ ≤ ∑' g, μ (P g) := measure_iUnion_le _
    _ = ∑' g, μ (Q g) := tsum_congr fun g => (measure_preimage_smul μ g⁻¹ (P g)).symm
    _ = μ (⋃ g, Q g) := (measure_iUnion₀ h2 hQm).symm
    _ ≤ μ B := measure_mono <| iUnion_subset fun g y hy => by simpa using hy.1.2

end Comparison

section Quot

variable {G X : Type*} [Group G] [MulAction G X] [MeasurableSpace X] {μ : Measure X}

@[to_additive addQuotMeasure  ]
noncomputable def quotMeasure (G : Type*) {X : Type*} [Group G] [MulAction G X] [MeasurableSpace X]
    (μ : Measure X) : Measure (Quotient (MulAction.orbitRel G X)) :=
  ⨆ (D : Set X) (_ : NullMeasurableSet D μ)
    (_ : ∀ᵐ x ∂μ, x ∈ D → ∀ g : G, g • x ∈ D → g • x = x),
    (μ.restrict D).map (Quotient.mk (MulAction.orbitRel G X))

@[to_additive map_restrict_le_addQuotMeasure]
theorem map_restrict_le_quotMeasure {D : Set X} (hD : NullMeasurableSet D μ)
    (hu : ∀ᵐ x ∂μ, x ∈ D → ∀ g : G, g • x ∈ D → g • x = x) :
    (μ.restrict D).map (Quotient.mk (MulAction.orbitRel G X)) ≤ quotMeasure G μ :=
  le_iSup_of_le D (le_iSup_of_le hD (le_iSup_of_le hu le_rfl))

@[to_additive isAEAddOrbitSection_of_forall  ]
theorem isAEOrbitSection_of_forall {D : Set X} (hD : MeasurableSet D) (hc : ∀ x, ∃ g : G, g • x ∈ D)
    (hu : ∀ x ∈ D, ∀ g : G, g • x ∈ D → g • x = x) (μ : Measure X) : IsAEOrbitSection G D μ :=
  ⟨hD.nullMeasurableSet, Eventually.of_forall hc, Eventually.of_forall hu⟩

@[to_additive IsAEAddOrbitSection.of_sameOrbits  ]
theorem IsAEOrbitSection.of_sameOrbits {H : Type*} [SMul H X] {D : Set X}
    (hD : IsAEOrbitSection H D μ) (h₁ : ∀ (h : H) (x : X), ∃ g : G, g • x = h • x)
    (h₂ : ∀ (g : G) (x : X), ∃ h : H, h • x = g • x) : IsAEOrbitSection G D μ where
  nullMeasurableSet := hD.nullMeasurableSet
  ae_covers := by
    filter_upwards [hD.ae_covers] with x ⟨h, hh⟩
    obtain ⟨g, hg⟩ := h₁ h x
    exact ⟨g, hg ▸ hh⟩
  ae_unique := by
    filter_upwards [hD.ae_unique] with x hx hxD g hg
    obtain ⟨h, hh⟩ := h₂ g x
    rw [← hh] at hg ⊢
    exact hx hxD h hg

@[to_additive isAEAddOrbitSection_of_isAddFundamentalDomain
]
theorem isAEOrbitSection_of_isFundamentalDomain [Countable G] {D : Set X}
    (hD : IsFundamentalDomain G D μ) : IsAEOrbitSection G D μ where
  nullMeasurableSet := hD.nullMeasurableSet
  ae_covers := hD.ae_covers
  ae_unique := by
    have : ∀ᵐ x ∂μ, ∀ g : G, x ∈ D → g • x ∈ D → g • x = x := by
      refine ae_all_iff.2 fun g => ?_
      by_cases hg : g = 1
      · exact Eventually.of_forall fun x _ _ => by rw [hg, one_smul]
      · have := hD.aedisjoint (inv_ne_one.2 hg)
        refine measure_mono_null (fun x hx => ?_) this
        simp only [mem_compl_iff, mem_setOf_eq, Classical.not_imp] at hx
        refine ⟨?_, ?_⟩
        · rw [mem_smul_set_iff_inv_smul_mem, inv_inv]; exact hx.2.1
        · simpa using hx.1
    filter_upwards [this] with x hx hxD g hg using hx g hxD hg

@[to_additive isAEAddOrbitSection_of_isAddFundamentalDomain_of_surjective
]
theorem isAEOrbitSection_of_isFundamentalDomain_of_surjective [Countable G] {Q : Type*} [Group Q]
    [MulAction Q X] (φ : G →* Q) (hφ : Function.Surjective φ) (hact : ∀ g (x : X), φ g • x = g • x)
    {D : Set X} (hD : IsFundamentalDomain Q D μ) : IsAEOrbitSection G D μ := by
  have : Countable Q := hφ.countable
  refine (isAEOrbitSection_of_isFundamentalDomain hD).of_sameOrbits (fun q x => ?_)
    fun g x => ⟨φ g, hact g x⟩
  obtain ⟨g, rfl⟩ := hφ q
  exact ⟨g, (hact g x).symm⟩

@[to_additive isAddFundamentalDomain_of_addOrbitSection
]
theorem isFundamentalDomain_of_orbitSection {D : Set X} (hD : NullMeasurableSet D μ)
    (hc : ∀ᵐ x ∂μ, ∃ g : G, g • x ∈ D) (hu : ∀ x ∈ D, ∀ g : G, g • x ∈ D → g • x = x)
    (hfree : ∀ g : G, g ≠ 1 → μ {x | g • x = x} = 0) : IsFundamentalDomain G D μ where
  nullMeasurableSet := hD
  ae_covers := hc
  aedisjoint g h hgh := by
    refine measure_mono_null (fun y hy => ?_) (hfree (g * h⁻¹) fun e => hgh (mul_inv_eq_one.1 e))
    obtain ⟨hg, hh⟩ := hy
    rw [mem_smul_set_iff_inv_smul_mem] at hg hh
    have := hu _ hg (h⁻¹ * g) (by simpa [mul_smul] using hh)
    rw [mul_smul, smul_inv_smul] at this
    rw [mem_setOf_eq, mul_smul, this, smul_inv_smul]

variable [Countable G] [MeasurableConstSMul G X] [SMulInvariantMeasure G X μ]

@[to_additive IsAEAddOrbitSection.isAddFundamentalDomain
]
theorem IsAEOrbitSection.isFundamentalDomain {D : Set X} (hD : IsAEOrbitSection G D μ)
    (hfree : ∀ g : G, g ≠ 1 → μ {x | g • x = x} = 0) : IsFundamentalDomain G D μ := by
  refine IsFundamentalDomain.mk'' hD.nullMeasurableSet hD.ae_covers (fun g hg => ?_)
    fun g => (measurePreserving_smul g μ).quasiMeasurePreserving
  have h1 : ∀ᵐ x ∂μ, ¬ g⁻¹ • x = x := by
    rw [ae_iff]; simpa using hfree g⁻¹ (inv_ne_one.2 hg)
  refine measure_mono_null (fun y hy => ?_) (h1.and hD.ae_unique)
  rintro ⟨h2, h3⟩
  exact h2 (h3 hy.2 g⁻¹ (mem_smul_set_iff_inv_smul_mem.1 hy.1))

@[to_additive measure_fixed_eq_zero_of_isAddFundamentalDomain
]
theorem measure_fixed_eq_zero_of_isFundamentalDomain {D : Set X} (hD : IsFundamentalDomain G D μ)
    {g : G} (hg : g ≠ 1) : μ {x | g • x = x} = 0 := by
  have h1 : ∀ᵐ x ∂μ, ∀ k : G, k • x ∈ D → ¬ g • x = x := by
    refine ae_all_iff.2 fun k => ?_
    have hne : k⁻¹ ≠ (k * g)⁻¹ := fun e => hg (by simpa using inv_injective e)
    refine measure_mono_null (fun x hx => ?_) (hD.aedisjoint hne)
    simp only [mem_compl_iff, mem_setOf_eq, Classical.not_imp, not_not] at hx
    refine ⟨?_, ?_⟩
    · rw [mem_smul_set_iff_inv_smul_mem, inv_inv]; exact hx.1
    · rw [mem_smul_set_iff_inv_smul_mem, inv_inv, mul_smul, hx.2]; exact hx.1
  refine measure_mono_null (fun x hx => ?_) (h1.and hD.ae_covers)
  rintro ⟨h2, k, hk⟩
  exact h2 k hk hx

@[to_additive map_restrict_le_map_restrict_of_ae_unique_of_ae_covers_add]
theorem map_restrict_le_map_restrict_of_ae_unique_of_ae_covers {S B : Set X}
    (hS : NullMeasurableSet S μ) (hB : NullMeasurableSet B μ)
    (hu : ∀ᵐ x ∂μ, x ∈ S → ∀ g : G, g • x ∈ S → g • x = x) (hc : ∀ᵐ x ∂μ, ∃ g : G, g • x ∈ B) :
    (μ.restrict S).map (Quotient.mk (MulAction.orbitRel G X)) ≤
      (μ.restrict B).map (Quotient.mk (MulAction.orbitRel G X)) := by
  refine Measure.le_iff.2 fun U hU => ?_
  rw [measure_map_restrict_apply μ S hU, measure_map_restrict_apply μ B hU]
  have hU' : NullMeasurableSet (Quotient.mk (MulAction.orbitRel G X) ⁻¹' U) μ :=
    (measurableSet_quotient.1 hU).nullMeasurableSet
  refine measure_le_of_ae_unique_of_ae_covers (G := G) (hU'.inter hS) (hU'.inter hB) ?_ ?_
  · filter_upwards [hu] with x hx hxS g hg using hx hxS.2 g hg.2
  · filter_upwards [hc] with x ⟨g, hg⟩ hxS
    refine ⟨g, ?_, hg⟩
    have : Quotient.mk (MulAction.orbitRel G X) (g • x) = Quotient.mk (MulAction.orbitRel G X) x :=
      Quotient.sound ⟨g, rfl⟩
    rw [mem_preimage, this]
    exact hxS.1

@[to_additive addQuotMeasure_le_map_restrict
]
theorem quotMeasure_le_map_restrict {B : Set X} (hB : NullMeasurableSet B μ)
    (hc : ∀ᵐ x ∂μ, ∃ g : G, g • x ∈ B) :
    quotMeasure G μ ≤ (μ.restrict B).map (Quotient.mk (MulAction.orbitRel G X)) :=
  iSup_le fun _ => iSup_le fun hS => iSup_le fun hu =>
    map_restrict_le_map_restrict_of_ae_unique_of_ae_covers hS hB hu hc

@[to_additive addQuotMeasure_univ_le
]
theorem quotMeasure_univ_le {B : Set X} (hB : NullMeasurableSet B μ)
    (hc : ∀ᵐ x ∂μ, ∃ g : G, g • x ∈ B) : quotMeasure G μ univ ≤ μ B := by
  refine (quotMeasure_le_map_restrict hB hc univ).trans_eq ?_
  rw [measure_map_restrict_apply μ B MeasurableSet.univ, preimage_univ, univ_inter]

namespace IsAEOrbitSection

variable {D D' : Set X}

@[to_additive IsAEAddOrbitSection.addQuotMeasure_eq
]
theorem quotMeasure_eq (hD : IsAEOrbitSection G D μ) :
    quotMeasure G μ = (μ.restrict D).map (Quotient.mk (MulAction.orbitRel G X)) :=
  le_antisymm (quotMeasure_le_map_restrict hD.nullMeasurableSet hD.ae_covers)
    (map_restrict_le_quotMeasure hD.nullMeasurableSet hD.ae_unique)

@[to_additive IsAEAddOrbitSection.map_restrict_eq
]
theorem map_restrict_eq (hD : IsAEOrbitSection G D μ) (hD' : IsAEOrbitSection G D' μ) :
    (μ.restrict D).map (Quotient.mk (MulAction.orbitRel G X)) =
      (μ.restrict D').map (Quotient.mk (MulAction.orbitRel G X)) :=
  hD.quotMeasure_eq.symm.trans hD'.quotMeasure_eq

@[to_additive IsAEAddOrbitSection.measurePreserving_mk]
theorem measurePreserving_mk (hD : IsAEOrbitSection G D μ) :
    MeasurePreserving (Quotient.mk (MulAction.orbitRel G X)) (μ.restrict D) (quotMeasure G μ) :=
  ⟨measurable_quotient_mk' (s := MulAction.orbitRel G X), hD.quotMeasure_eq.symm⟩

@[to_additive IsAEAddOrbitSection.addQuotMeasure_apply]
theorem quotMeasure_apply (hD : IsAEOrbitSection G D μ)
    {U : Set (Quotient (MulAction.orbitRel G X))} (hU : MeasurableSet U) :
    quotMeasure G μ U = μ (Quotient.mk (MulAction.orbitRel G X) ⁻¹' U ∩ D) := by
  rw [hD.quotMeasure_eq, measure_map_restrict_apply μ D hU]

@[to_additive IsAEAddOrbitSection.addQuotMeasure_univ]
theorem quotMeasure_univ (hD : IsAEOrbitSection G D μ) : quotMeasure G μ univ = μ D := by
  rw [hD.quotMeasure_apply MeasurableSet.univ, preimage_univ, univ_inter]

@[to_additive IsAEAddOrbitSection.measure_eq]
theorem measure_eq (hD : IsAEOrbitSection G D μ) (hD' : IsAEOrbitSection G D' μ) : μ D = μ D' :=
  hD.quotMeasure_univ.symm.trans hD'.quotMeasure_univ

@[to_additive IsAEAddOrbitSection.lintegral_addQuotMeasure]
theorem lintegral_quotMeasure (hD : IsAEOrbitSection G D μ)
    {f : Quotient (MulAction.orbitRel G X) → ℝ≥0∞} (hf : AEMeasurable f (quotMeasure G μ)) :
    ∫⁻ q, f q ∂quotMeasure G μ = ∫⁻ x in D, f (Quotient.mk _ x) ∂μ := by
  rw [hD.quotMeasure_eq] at hf ⊢
  exact lintegral_map' hf hD.measurePreserving_mk.measurable.aemeasurable

@[to_additive IsAEAddOrbitSection.integral_addQuotMeasure]
theorem integral_quotMeasure (hD : IsAEOrbitSection G D μ) {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {f : Quotient (MulAction.orbitRel G X) → E}
    (hf : AEStronglyMeasurable f (quotMeasure G μ)) :
    ∫ q, f q ∂quotMeasure G μ = ∫ x in D, f (Quotient.mk _ x) ∂μ := by
  rw [hD.quotMeasure_eq] at hf ⊢
  exact integral_map hD.measurePreserving_mk.measurable.aemeasurable hf

@[to_additive IsAEAddOrbitSection.integrable_addQuotMeasure_iff]
theorem integrable_quotMeasure_iff (hD : IsAEOrbitSection G D μ) {E : Type*} [NormedAddCommGroup E]
    {f : Quotient (MulAction.orbitRel G X) → E} (hf : AEStronglyMeasurable f (quotMeasure G μ)) :
    Integrable f (quotMeasure G μ) ↔ IntegrableOn (fun x => f (Quotient.mk _ x)) D μ :=
  (hD.measurePreserving_mk.integrable_comp hf).symm

@[to_additive IsAEAddOrbitSection.addQuotMeasure_apply_eq_zero_iff
]
theorem quotMeasure_apply_eq_zero_iff (hD : IsAEOrbitSection G D μ)
    {U : Set (Quotient (MulAction.orbitRel G X))} (hU : MeasurableSet U) :
    quotMeasure G μ U = 0 ↔ μ (Quotient.mk (MulAction.orbitRel G X) ⁻¹' U) = 0 := by
  rw [hD.quotMeasure_apply hU]
  refine ⟨fun h => ?_, fun h => measure_mono_null inter_subset_left h⟩
  have h1 : ∀ᵐ x ∂μ, ∀ g : G, g • x ∉ Quotient.mk (MulAction.orbitRel G X) ⁻¹' U ∩ D :=
    ae_all_iff.2 fun g => (measurePreserving_smul g μ).quasiMeasurePreserving.ae
      (p := fun x => x ∉ Quotient.mk (MulAction.orbitRel G X) ⁻¹' U ∩ D)
      (measure_eq_zero_iff_ae_notMem.1 h)
  refine measure_mono_null (fun x hx => ?_) (h1.and hD.ae_covers)
  rintro ⟨h2, g, hg⟩
  refine h2 g ⟨?_, hg⟩
  have : Quotient.mk (MulAction.orbitRel G X) (g • x) = Quotient.mk (MulAction.orbitRel G X) x :=
    Quotient.sound ⟨g, rfl⟩
  rw [mem_preimage, this]
  exact hx

@[to_additive IsAEAddOrbitSection.addQuotMeasure_eq_zero_iff]
theorem quotMeasure_eq_zero_iff (hD : IsAEOrbitSection G D μ) : quotMeasure G μ = 0 ↔ μ = 0 := by
  rw [← Measure.measure_univ_eq_zero, hD.quotMeasure_apply_eq_zero_iff MeasurableSet.univ,
    preimage_univ, Measure.measure_univ_eq_zero]

@[to_additive IsAEAddOrbitSection.addQuotMeasure_image_le
]
theorem quotMeasure_image_le (hD : IsAEOrbitSection G D μ) {A : Set X} (hA : MeasurableSet A) :
    MeasurableSet (Quotient.mk (MulAction.orbitRel G X) '' A) ∧
      quotMeasure G μ (Quotient.mk (MulAction.orbitRel G X) '' A) ≤ μ A := by
  have hm : MeasurableSet (Quotient.mk (MulAction.orbitRel G X) '' A) := by
    have : Quotient.mk (MulAction.orbitRel G X) ⁻¹' Quotient.mk (MulAction.orbitRel G X) '' A = _ :=
      MulAction.quotient_preimage_image_eq_union_mul A (G := G)
    rw [measurableSet_quotient, Quotient.mk''_eq_mk, this]
    exact MeasurableSet.iUnion fun g => hA.const_smul g
  refine ⟨hm, ?_⟩
  rw [hD.quotMeasure_apply hm]
  refine measure_le_of_ae_unique_of_ae_covers (G := G)
    ((measurableSet_quotient.1 hm).nullMeasurableSet.inter hD.nullMeasurableSet)
    hA.nullMeasurableSet ?_ (Eventually.of_forall ?_)
  · filter_upwards [hD.ae_unique] with x hx hxS g hg using hx hxS.2 g hg.2
  · rintro x ⟨⟨a, ha, hax⟩, -⟩
    obtain ⟨g, hg⟩ := Quotient.exact hax
    exact ⟨g, (show g • x = a from hg) ▸ ha⟩

@[to_additive IsAEAddOrbitSection.sigmaFinite_addQuotMeasure]
theorem sigmaFinite_quotMeasure (hD : IsAEOrbitSection G D μ) [SigmaFinite μ] :
    SigmaFinite (quotMeasure G μ) := by
  refine ⟨⟨⟨fun n => Quotient.mk (MulAction.orbitRel G X) '' spanningSets μ n, fun _ => trivial,
    fun n => ?_, ?_⟩⟩⟩
  · exact (hD.quotMeasure_image_le (measurableSet_spanningSets μ n)).2.trans_lt
      (measure_spanningSets_lt_top μ n)
  · rw [← image_iUnion, iUnion_spanningSets]
    exact image_univ_of_surjective Quotient.mk_surjective

end IsAEOrbitSection

@[to_additive addQuotMeasure_eq_of_isAddFundamentalDomain
]
theorem quotMeasure_eq_of_isFundamentalDomain {D : Set X} (hD : IsFundamentalDomain G D μ) :
    quotMeasure G μ = (μ.restrict D).map (Quotient.mk (MulAction.orbitRel G X)) :=
  (isAEOrbitSection_of_isFundamentalDomain hD).quotMeasure_eq

@[to_additive addQuotMeasure_addQuotientMeasureEqMeasurePreimage]
instance quotMeasure_quotientMeasureEqMeasurePreimage :
    QuotientMeasureEqMeasurePreimage μ (quotMeasure G μ) :=
  ⟨fun _ h => quotMeasure_eq_of_isFundamentalDomain h⟩

@[to_additive addQuotMeasure_univ_eq_addCovolume
]
theorem quotMeasure_univ_eq_covolume [h : HasFundamentalDomain G X μ] :
    quotMeasure G μ univ = covolume G X μ := by
  obtain ⟨D, hD⟩ := h.ExistsIsFundamentalDomain
  rw [(isAEOrbitSection_of_isFundamentalDomain hD).quotMeasure_univ, hD.covolume_eq_volume]

@[to_additive lintegral_eq_lintegral_addQuotMeasure_tsum
]
theorem lintegral_eq_lintegral_quotMeasure_tsum [h : HasFundamentalDomain G X μ] {f : X → ℝ≥0∞}
    (hf : Measurable f) {F : Quotient (MulAction.orbitRel G X) → ℝ≥0∞}
    (hF : ∀ x, F (Quotient.mk _ x) = ∑' g : G, f (g • x)) :
    ∫⁻ x, f x ∂μ = ∫⁻ q, F q ∂quotMeasure G μ := by
  obtain ⟨D, hD⟩ := h.ExistsIsFundamentalDomain
  have hm : ∀ g : G, Measurable fun x => f (g • x) := fun g => hf.comp (measurable_const_smul g)
  have hFm : Measurable F := by
    refine measurable_from_quotient.2 ?_
    have : F ∘ Quotient.mk'' = fun x => ∑' g : G, f (g • x) := funext hF
    rw [this]
    exact Measurable.tsum hm
  rw [(isAEOrbitSection_of_isFundamentalDomain hD).lintegral_quotMeasure hFm.aemeasurable,
    hD.lintegral_eq_tsum'' f, ← lintegral_tsum fun g => (hm g).aemeasurable]
  simp only [hF]

end Quot

section ProperlyDiscontinuous

variable (G X : Type*) [Group G] [Countable G] [MulAction G X] [TopologicalSpace X] [T2Space X]
  [SecondCountableTopology X] [LocallyCompactSpace X] [MeasurableSpace X] [BorelSpace X]
  [ContinuousConstSMul G X]

@[to_additive exists_measurableSet_addOrbitSection
]
theorem exists_measurableSet_orbitSection [ProperlyDiscontinuousSMul G X] :
    ∃ D : Set X, MeasurableSet D ∧ (∀ x, ∃ g : G, g • x ∈ D) ∧
      ∀ x ∈ D, ∀ g : G, g • x ∈ D → g • x = x := by
  refine exists_measurableSet_orbitSection_of_discreteOrbits
    (fun g => (isClosed_eq (continuous_const_smul g) continuous_id).measurableSet) fun x => ?_
  obtain ⟨U, hU, h⟩ := ProperlyDiscontinuousSMul.exists_nhds_image_smul_eq_self G x
  exact ⟨U, hU, fun g hg => h g ⟨g • x, ⟨x, mem_of_mem_nhds hU, rfl⟩, hg⟩⟩

@[to_additive exists_isAddFundamentalDomain_of_free
]
theorem exists_isFundamentalDomain_of_free [ProperlyDiscontinuousSMul G X]
    (hfree : ∀ (g : G) (x : X), g • x = x → g = 1) :
    ∃ D : Set X, MeasurableSet D ∧ (∀ x, ∃! g : G, g • x ∈ D) ∧
      ∀ μ : Measure X, IsFundamentalDomain G D μ := by
  obtain ⟨D, hD, hc, hu⟩ := exists_measurableSet_orbitSection G X
  have h : ∀ x, ∃! g : G, g • x ∈ D := fun x => by
    obtain ⟨g, hg⟩ := hc x
    refine ⟨g, hg, fun k hk => ?_⟩
    have := hu _ hg (k * g⁻¹) (by simpa [mul_smul] using hk)
    exact mul_inv_eq_one.1 (hfree _ _ this)
  exact ⟨D, hD, h, fun μ => IsFundamentalDomain.mk' hD.nullMeasurableSet h⟩

variable {X}

@[to_additive exists_isAEAddOrbitSection]
theorem exists_isAEOrbitSection [ProperlyDiscontinuousSMul G X] (μ : Measure X) :
    ∃ D : Set X, MeasurableSet D ∧ IsAEOrbitSection G D μ := by
  obtain ⟨D, hD, hc, hu⟩ := exists_measurableSet_orbitSection G X
  exact ⟨D, hD, isAEOrbitSection_of_forall hD hc hu μ⟩

@[to_additive exists_isAddFundamentalDomain_of_ae_free
]
theorem exists_isFundamentalDomain_of_ae_free [ProperlyDiscontinuousSMul G X] (μ : Measure X)
    (hfree : μ {x | MulAction.stabilizer G x ≠ ⊥} = 0) :
    ∃ D : Set X, MeasurableSet D ∧ (∀ x, ∃ g : G, g • x ∈ D) ∧
      (∀ x ∈ D, ∀ g : G, g • x ∈ D → g • x = x) ∧ IsFundamentalDomain G D μ := by
  obtain ⟨D, hD, hc, hu⟩ := exists_measurableSet_orbitSection G X
  refine ⟨D, hD, hc, hu, isFundamentalDomain_of_orbitSection hD.nullMeasurableSet
    (Eventually.of_forall hc) hu fun g hg => measure_mono_null (fun x hx => ?_) hfree⟩
  refine fun h : MulAction.stabilizer G x = ⊥ => hg ?_
  have : g ∈ MulAction.stabilizer G x := hx
  simpa [h] using this

@[to_additive exists_isAddFundamentalDomain_of_surjective
]
theorem exists_isFundamentalDomain_of_surjective [ProperlyDiscontinuousSMul G X] {Q : Type*}
    [Group Q] [MulAction Q X] (φ : G →* Q) (hφ : Function.Surjective φ)
    (hact : ∀ g (x : X), φ g • x = g • x) (μ : Measure X)
    (hfree : ∀ g : G, φ g ≠ 1 → μ {x | g • x = x} = 0) :
    ∃ D : Set X, MeasurableSet D ∧ (∀ x, ∃ g : G, g • x ∈ D) ∧
      (∀ x ∈ D, ∀ g : G, g • x ∈ D → g • x = x) ∧ IsFundamentalDomain Q D μ := by
  obtain ⟨D, hD, hc, hu⟩ := exists_measurableSet_orbitSection G X
  refine ⟨D, hD, hc, hu, isFundamentalDomain_of_orbitSection hD.nullMeasurableSet
    (Eventually.of_forall fun x => ?_) (fun x hx q hq => ?_) fun q hq => ?_⟩
  · obtain ⟨g, hg⟩ := hc x
    exact ⟨φ g, by rwa [hact]⟩
  · obtain ⟨g, rfl⟩ := hφ q
    rw [hact] at hq ⊢
    exact hu x hx g hq
  · obtain ⟨g, rfl⟩ := hφ q
    simpa only [hact] using hfree g hq

theorem exists_isFundamentalDomain_range_toPermHom [ProperlyDiscontinuousSMul G X] (μ : Measure X)
    (hfree : ∀ g : G, (∃ x : X, g • x ≠ x) → μ {x | g • x = x} = 0) :
    ∃ D : Set X, MeasurableSet D ∧ (∀ x, ∃ g : G, g • x ∈ D) ∧
      (∀ x ∈ D, ∀ g : G, g • x ∈ D → g • x = x) ∧
      IsFundamentalDomain (MulAction.toPermHom G X).range D μ := by
  refine exists_isFundamentalDomain_of_surjective G (MulAction.toPermHom G X).rangeRestrict
    (MonoidHom.rangeRestrict_surjective _) (fun _ _ => rfl) μ fun g hg => hfree g ?_
  by_contra h
  push Not at h
  exact hg (Subtype.ext (Equiv.ext h))

@[to_additive exists_isAddFundamentalDomain_and_addQuotMeasure_eq
]
theorem exists_isFundamentalDomain_and_quotMeasure_eq [ProperlyDiscontinuousSMul G X]
    (μ : Measure X) [SMulInvariantMeasure G X μ]
    (hfree : μ {x | MulAction.stabilizer G x ≠ ⊥} = 0) :
    (∃ D : Set X, MeasurableSet D ∧ IsFundamentalDomain G D μ) ∧
      ∀ D : Set X, IsFundamentalDomain G D μ →
        (μ.restrict D).map (Quotient.mk (MulAction.orbitRel G X)) = quotMeasure G μ := by
  obtain ⟨D, hD, -, -, h⟩ := exists_isFundamentalDomain_of_ae_free G μ hfree
  exact ⟨⟨D, hD, h⟩, fun D h => (quotMeasure_eq_of_isFundamentalDomain h).symm⟩

@[to_additive addQuotMeasure_eq_zero_iff
]
theorem quotMeasure_eq_zero_iff [ProperlyDiscontinuousSMul G X] (μ : Measure X)
    [SMulInvariantMeasure G X μ] : quotMeasure G μ = 0 ↔ μ = 0 := by
  obtain ⟨D, -, hD⟩ := exists_isAEOrbitSection G μ
  exact hD.quotMeasure_eq_zero_iff

end ProperlyDiscontinuous

section DiscreteSubgroup

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [SecondCountableTopology G] (Γ : Subgroup G) [DiscreteTopology Γ]

@[to_additive countable_of_discrete_addSubgroup
]
theorem countable_of_discrete_subgroup : Countable Γ :=
  TopologicalSpace.separableSpace_iff_countable.1 inferInstance

omit [IsTopologicalGroup G] [SecondCountableTopology G] in
@[to_additive exists_nhds_zero_inter_addSubgroup]
theorem exists_nhds_one_inter_subgroup : ∃ V ∈ 𝓝 (1 : G), ∀ g ∈ Γ, g ∈ V → g = 1 := by
  have h : ({1} : Set Γ) ∈ 𝓝 (1 : Γ) := (isOpen_discrete _).mem_nhds rfl
  rw [nhds_induced, mem_comap] at h
  obtain ⟨V, hV, h⟩ := h
  exact ⟨V, hV, fun g hg hgV => congrArg Subtype.val (h (a := ⟨g, hg⟩) hgV)⟩

variable [MeasurableSpace G] [BorelSpace G]

@[to_additive exists_isAddFundamentalDomain_addSubgroup
]
theorem exists_isFundamentalDomain_subgroup :
    ∃ D : Set G, MeasurableSet D ∧ (∀ x, ∃! g : Γ, g • x ∈ D) ∧
      ∀ μ : Measure G, IsFundamentalDomain Γ D μ := by
  have := countable_of_discrete_subgroup Γ
  have hfree : ∀ (g : Γ) (x : G), g • x = x → g = 1 := fun g x h =>
    Subtype.ext (mul_eq_right.1 h)
  obtain ⟨V, hV, hV1⟩ := exists_nhds_one_inter_subgroup Γ
  obtain ⟨D, hD, hc, hu⟩ := exists_measurableSet_orbitSection_of_discreteOrbits (G := Γ) (X := G)
    (fun g => by
      by_cases hg : g = 1
      · simp [hg]
      · have : {x : G | g • x = x} = ∅ := eq_empty_of_forall_notMem fun x hx => hg (hfree g x hx)
        simp [this])
    (fun x => by
      refine ⟨(· * x⁻¹) ⁻¹' V, (continuous_mul_const _).continuousAt.preimage_mem_nhds
        (by simpa using hV), fun g hg => ?_⟩
      have h1 : (g : G) ∈ V := by
        have : (g : G) * x * x⁻¹ ∈ V := hg
        simpa using this
      have : g = 1 := Subtype.ext (hV1 g g.2 h1)
      rw [this, one_smul])
  have h : ∀ x, ∃! g : Γ, g • x ∈ D := fun x => by
    obtain ⟨g, hg⟩ := hc x
    refine ⟨g, hg, fun k hk => ?_⟩
    have := hu _ hg (k * g⁻¹) (by rwa [mul_smul, inv_smul_smul])
    exact mul_inv_eq_one.1 (hfree _ _ this)
  exact ⟨D, hD, h, fun μ => IsFundamentalDomain.mk' hD.nullMeasurableSet h⟩

@[to_additive exists_isAddFundamentalDomain_addSubgroup_op
]
theorem exists_isFundamentalDomain_subgroup_op :
    ∃ D : Set G, MeasurableSet D ∧ (∀ x, ∃! g : Γ.op, g • x ∈ D) ∧
      ∀ μ : Measure G, IsFundamentalDomain Γ.op D μ := by
  obtain ⟨D, hD, h, -⟩ := exists_isFundamentalDomain_subgroup Γ
  have h' : ∀ x, ∃! g : Γ.op, g • x ∈ D⁻¹ := fun x => by
    obtain ⟨g, hg, hu⟩ := h x⁻¹
    refine ⟨⟨MulOpposite.op (g : G)⁻¹, inv_mem g.2⟩, ?_, fun k hk => ?_⟩
    · have : (g : G) * x⁻¹ ∈ D := hg
      change (x * (g : G)⁻¹)⁻¹ ∈ D
      rwa [mul_inv_rev, inv_inv]
    · have hk' : (x * MulOpposite.unop (k : Gᵐᵒᵖ))⁻¹ ∈ D := hk
      rw [mul_inv_rev] at hk'
      have := hu ⟨(MulOpposite.unop (k : Gᵐᵒᵖ))⁻¹, inv_mem k.2⟩ hk'
      subst this
      ext
      simp
  exact ⟨D⁻¹, hD.inv, h', fun μ => IsFundamentalDomain.mk' hD.inv.nullMeasurableSet h'⟩

@[to_additive hasAddFundamentalDomain_addSubgroup]
theorem hasFundamentalDomain_subgroup (μ : Measure G) : HasFundamentalDomain Γ G μ := by
  obtain ⟨D, -, -, h⟩ := exists_isFundamentalDomain_subgroup Γ
  exact ⟨D, h μ⟩

@[to_additive hasAddFundamentalDomain_addSubgroup_op]
theorem hasFundamentalDomain_subgroup_op (μ : Measure G) : HasFundamentalDomain Γ.op G μ := by
  obtain ⟨D, -, -, h⟩ := exists_isFundamentalDomain_subgroup_op Γ
  exact ⟨D, h μ⟩

@[to_additive exists_isAddFundamentalDomain_and_addQuotMeasure_eq_addSubgroup
]
theorem exists_isFundamentalDomain_and_quotMeasure_eq_subgroup (μ : Measure G)
    [μ.IsMulLeftInvariant] :
    (∃ D : Set G, MeasurableSet D ∧ IsFundamentalDomain Γ D μ) ∧
      ∀ D : Set G, IsFundamentalDomain Γ D μ →
        (μ.restrict D).map (Quotient.mk (MulAction.orbitRel Γ G)) = quotMeasure Γ μ := by
  have := countable_of_discrete_subgroup Γ
  obtain ⟨D, hD, -, h⟩ := exists_isFundamentalDomain_subgroup Γ
  exact ⟨⟨D, hD, h μ⟩, fun D h => (quotMeasure_eq_of_isFundamentalDomain h).symm⟩

@[to_additive exists_isAddFundamentalDomain_and_addQuotMeasure_eq_addSubgroup_op
]
theorem exists_isFundamentalDomain_and_quotMeasure_eq_subgroup_op (μ : Measure G)
    [μ.IsMulRightInvariant] :
    (∃ D : Set G, MeasurableSet D ∧ IsFundamentalDomain Γ.op D μ) ∧
      ∀ D : Set G, IsFundamentalDomain Γ.op D μ →
        (μ.restrict D).map (Quotient.mk (MulAction.orbitRel Γ.op G)) = quotMeasure Γ.op μ := by
  have := countable_of_discrete_subgroup Γ
  obtain ⟨D, hD, -, h⟩ := exists_isFundamentalDomain_subgroup_op Γ
  exact ⟨⟨D, hD, h μ⟩, fun D h => (quotMeasure_eq_of_isFundamentalDomain h).symm⟩

end DiscreteSubgroup

theorem properlyDiscontinuousSMul_of_discrete_of_properSMul {G X : Type*} [Group G]
    [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] [MulAction G X] [TopologicalSpace X]
    [T2Space X] [LocallyCompactSpace X] [ProperSMul G X] (Γ : Subgroup G) [DiscreteTopology Γ] :
    ProperlyDiscontinuousSMul Γ X := by
  have : IsClosed (Γ : Set G) := Subgroup.isClosed_of_discrete
  have : ContinuousSMul G X := ProperSMul.toContinuousSMul
  rw [properlyDiscontinuousSMul_iff_properSMul]
  infer_instance

theorem addQuotMeasure_zmultiples_one_univ :
    addQuotMeasure (AddSubgroup.zmultiples (1 : ℝ)) (volume : Measure ℝ) univ = 1 := by
  rw [isAEAddOrbitSection_zmultiples_Ico.addQuotMeasure_univ]
  simp

end GlobalTheory
