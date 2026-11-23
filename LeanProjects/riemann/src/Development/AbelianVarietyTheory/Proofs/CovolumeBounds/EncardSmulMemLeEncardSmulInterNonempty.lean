import Mathlib

open MeasureTheory Set
open scoped ENNReal Pointwise

namespace GlobalTheory

section Multiplicity

variable {G X : Type*} [Group G] [MulAction G X]

@[to_additive
]
theorem encard_smul_mem_le_encard_smul_inter_nonempty (B : Set X) (x : X) :
    {g : G | g • x ∈ B}.encard ≤ {g : G | (g • B ∩ B).Nonempty}.encard := by
  rcases eq_empty_or_nonempty {g : G | g • x ∈ B} with h | ⟨g₀, hg₀⟩
  · simp [h]
  · refine Set.encard_le_encard_of_injOn (f := fun g => g * g₀⁻¹) ?_ ?_
    · intro g hg
      refine ⟨g • x, ⟨g₀ • x, hg₀, ?_⟩, hg⟩
      simp [smul_smul]
    · intro a _ b _ hab
      exact mul_right_cancel hab

variable [MeasurableSpace X] {μ : Measure X} [MeasurableConstSMul G X]
  [SMulInvariantMeasure G X μ] [Countable G] {B D : Set X}

omit [MeasurableSpace X] [MeasurableConstSMul G X] [Countable G] in

@[to_additive
]
theorem tsum_indicator_smul_eq_encard (B : Set X) (x : X) :
    ∑' g : G, ((fun y => g • y) ⁻¹' B).indicator (fun _ => (1 : ℝ≥0∞)) x
      = ({g : G | g • x ∈ B}.encard : ℝ≥0∞) := by
  rw [← ENNReal.tsum_set_one, tsum_subtype {g : G | g • x ∈ B} (fun _ => (1 : ℝ≥0∞))]
  refine tsum_congr fun g => ?_
  by_cases h : g • x ∈ B <;> simp [Set.indicator, h]

@[to_additive
]
theorem sum_restrict_preimage_smul_le (hB : NullMeasurableSet B μ) {m : ℝ≥0∞}
    (hm : ∀ᵐ x ∂μ.restrict D, ({g : G | g • x ∈ B}.encard : ℝ≥0∞) ≤ m) :
    (Measure.sum fun g : G => (μ.restrict D).restrict ((fun y => g • y) ⁻¹' B))
      ≤ m • μ.restrict D := by
  have hB' : ∀ g : G, NullMeasurableSet ((fun y => g • y) ⁻¹' B) (μ.restrict D) := fun g =>
    (hB.preimage (measurePreserving_smul g μ).quasiMeasurePreserving).mono
      Measure.restrict_le_self
  rw [Measure.le_iff]
  intro A hA
  rw [Measure.sum_apply _ hA, Measure.smul_apply, smul_eq_mul]
  have h1 : ∀ g : G, ((μ.restrict D).restrict ((fun y => g • y) ⁻¹' B)) A
      = ∫⁻ x in A, ((fun y => g • y) ⁻¹' B).indicator (fun _ => (1 : ℝ≥0∞)) x
          ∂(μ.restrict D) := by
    intro g
    rw [lintegral_indicator₀ ((hB' g).mono Measure.restrict_le_self), setLIntegral_one,
      Measure.restrict_apply hA,
      Measure.restrict_apply₀ ((hB' g).mono Measure.restrict_le_self), inter_comm]
  simp_rw [h1]
  rw [← lintegral_tsum fun g => (aemeasurable_const.indicator₀
    ((hB' g).mono Measure.restrict_le_self))]
  simp_rw [tsum_indicator_smul_eq_encard]
  calc ∫⁻ x in A, ({g : G | g • x ∈ B}.encard : ℝ≥0∞) ∂(μ.restrict D)
      ≤ ∫⁻ _ in A, m ∂(μ.restrict D) := lintegral_mono_ae (ae_restrict_of_ae hm)
    _ = m * (μ.restrict D) A := by rw [setLIntegral_const]

@[to_additive setLIntegral_le_mul_of_ae_covers_vadd
]
theorem setLIntegral_le_mul_of_ae_covers (hD : ∀ᵐ x ∂μ, ∃ g : G, g • x ∈ D)
    (hB : NullMeasurableSet B μ) {u : X → ℝ≥0∞} (hu : ∀ (g : G) (x : X), u (g • x) = u x)
    {m : ℝ≥0∞} (hm : ∀ᵐ x ∂μ.restrict D, ({g : G | g • x ∈ B}.encard : ℝ≥0∞) ≤ m) :
    ∫⁻ x in B, u x ∂μ ≤ m * ∫⁻ x in D, u x ∂μ := by
  have hcov : B ≤ᵐ[μ] (⋃ g : G, g • (((fun y => g • y) ⁻¹' B) ∩ D) : Set X) := by
    filter_upwards [hD] with x ⟨g, hg⟩ hx
    refine mem_iUnion.2 ⟨g⁻¹, g • x, ⟨?_, hg⟩, by simp⟩
    change g⁻¹ • g • x ∈ B
    rw [inv_smul_smul]
    exact hx
  have hB' : ∀ g : G, NullMeasurableSet ((fun y => g • y) ⁻¹' B) (μ.restrict D) := fun g =>
    (hB.preimage (measurePreserving_smul g μ).quasiMeasurePreserving).mono
      Measure.restrict_le_self
  calc ∫⁻ x in B, u x ∂μ
      ≤ ∫⁻ x in ⋃ g : G, g • (((fun y => g • y) ⁻¹' B) ∩ D), u x ∂μ :=
        lintegral_mono_set' hcov
    _ ≤ ∑' g : G, ∫⁻ x in g • (((fun y => g • y) ⁻¹' B) ∩ D), u x ∂μ := lintegral_iUnion_le _ _
    _ = ∑' g : G, ∫⁻ x, u x ∂((μ.restrict D).restrict ((fun y => g • y) ⁻¹' B)) := by
        refine tsum_congr fun g => ?_
        rw [Measure.restrict_restrict₀ (hB' g), ← image_smul,
          ← (measurePreserving_smul g μ).setLIntegral_comp_emb (measurableEmbedding_const_smul g)]
        simp only [hu]
    _ = ∫⁻ x, u x ∂(Measure.sum fun g : G =>
          (μ.restrict D).restrict ((fun y => g • y) ⁻¹' B)) := (lintegral_sum_measure _ _).symm
    _ ≤ ∫⁻ x, u x ∂(m • μ.restrict D) :=
        lintegral_mono' (sum_restrict_preimage_smul_le hB hm) le_rfl
    _ = m * ∫⁻ x in D, u x ∂μ := by rw [lintegral_smul_measure, smul_eq_mul]

@[to_additive setIntegral_le_mul_of_ae_covers_vadd
]
theorem setIntegral_le_mul_of_ae_covers (hD : ∀ᵐ x ∂μ, ∃ g : G, g • x ∈ D)
    (hB : NullMeasurableSet B μ) {u : X → ℝ} (hu : ∀ (g : G) (x : X), u (g • x) = u x)
    (hu0 : ∀ x, 0 ≤ u x) (huB : AEStronglyMeasurable u (μ.restrict B))
    (huD : IntegrableOn u D μ) {m : ℕ}
    (hm : ∀ᵐ x ∂μ.restrict D, {g : G | g • x ∈ B}.encard ≤ m) :
    IntegrableOn u B μ ∧ ∫ x in B, u x ∂μ ≤ m * ∫ x in D, u x ∂μ := by
  have key : ∫⁻ x in B, ENNReal.ofReal (u x) ∂μ ≤ m * ∫⁻ x in D, ENNReal.ofReal (u x) ∂μ := by
    refine setLIntegral_le_mul_of_ae_covers hD hB (fun g x => by rw [hu]) ?_
    filter_upwards [hm] with x hx
    exact_mod_cast ENat.toENNReal_le.2 hx
  have hfin : ∫⁻ x in D, ENNReal.ofReal (u x) ∂μ ≠ ⊤ :=
    ((hasFiniteIntegral_iff_ofReal (.of_forall hu0)).1 huD.2).ne
  have hfin' : (m : ℝ≥0∞) * ∫⁻ x in D, ENNReal.ofReal (u x) ∂μ ≠ ⊤ :=
    ENNReal.mul_ne_top (ENNReal.natCast_ne_top m) hfin
  refine ⟨⟨huB, (hasFiniteIntegral_iff_ofReal (.of_forall hu0)).2 (key.trans_lt hfin'.lt_top)⟩, ?_⟩
  rw [integral_eq_lintegral_of_nonneg_ae (.of_forall hu0) huB,
    integral_eq_lintegral_of_nonneg_ae (.of_forall hu0) huD.1]
  simpa [ENNReal.toReal_mul] using ENNReal.toReal_mono hfin' key

@[to_additive setLIntegral_le_mul_of_isAddFundamentalDomain
]
theorem setLIntegral_le_mul_of_isFundamentalDomain (hD : IsFundamentalDomain G D μ)
    (hB : NullMeasurableSet B μ) {u : X → ℝ≥0∞} (hu : ∀ (g : G) (x : X), u (g • x) = u x)
    {m : ℝ≥0∞} (hm : ∀ x, ({g : G | g • x ∈ B}.encard : ℝ≥0∞) ≤ m) :
    ∫⁻ x in B, u x ∂μ ≤ m * ∫⁻ x in D, u x ∂μ :=
  setLIntegral_le_mul_of_ae_covers hD.ae_covers hB hu (.of_forall hm)

@[to_additive setLIntegral_le_encard_mul_of_ae_covers_vadd
]
theorem setLIntegral_le_encard_mul_of_ae_covers (hD : ∀ᵐ x ∂μ, ∃ g : G, g • x ∈ D)
    (hB : NullMeasurableSet B μ) {u : X → ℝ≥0∞} (hu : ∀ (g : G) (x : X), u (g • x) = u x) :
    ∫⁻ x in B, u x ∂μ
      ≤ ({g : G | (g • B ∩ B).Nonempty}.encard : ℝ≥0∞) * ∫⁻ x in D, u x ∂μ :=
  setLIntegral_le_mul_of_ae_covers hD hB hu (.of_forall fun x =>
    ENat.toENNReal_le.2 (encard_smul_mem_le_encard_smul_inter_nonempty B x))

omit [MeasurableConstSMul G X] [SMulInvariantMeasure G X μ] in

@[to_additive ae_encard_vadd_mem_le_one
]
theorem ae_encard_smul_mem_le_one (hD : IsFundamentalDomain G D μ) :
    ∀ᵐ x ∂μ, {g : G | g • x ∈ D}.encard ≤ 1 := by
  have h : ∀ᵐ x ∂μ, ∀ g₁ g₂ : G, g₁ ≠ g₂ → x ∉ g₁ • D ∩ g₂ • D := by
    refine ae_all_iff.2 fun g₁ => ae_all_iff.2 fun g₂ => ?_
    by_cases h : g₁ = g₂
    · simp [h]
    · filter_upwards [measure_eq_zero_iff_ae_notMem.1 (hD.aedisjoint h)] with x hx _ using hx
  filter_upwards [h] with x hx
  rw [encard_le_one_iff]
  intro a b ha hb
  by_contra hab
  refine hx a⁻¹ b⁻¹ (by simpa using hab) ⟨?_, ?_⟩
  · rw [mem_smul_set_iff_inv_smul_mem, inv_inv]; exact ha
  · rw [mem_smul_set_iff_inv_smul_mem, inv_inv]; exact hb

@[to_additive setLIntegral_le_of_isAddFundamentalDomain_of_ae_covers
]
theorem setLIntegral_le_of_isFundamentalDomain_of_ae_covers {D' : Set X}
    (hD : IsFundamentalDomain G D μ) (hD' : ∀ᵐ x ∂μ, ∃ g : G, g • x ∈ D')
    {u : X → ℝ≥0∞} (hu : ∀ (g : G) (x : X), u (g • x) = u x) :
    ∫⁻ x in D, u x ∂μ ≤ ∫⁻ x in D', u x ∂μ := by
  have := setLIntegral_le_mul_of_ae_covers hD' hD.nullMeasurableSet hu (m := 1) (by
    filter_upwards [ae_restrict_of_ae (ae_encard_smul_mem_le_one hD)] with x hx
    exact_mod_cast ENat.toENNReal_le.2 hx)
  simpa using this

@[to_additive measure_le_of_isAddFundamentalDomain_of_ae_covers
]
theorem measure_le_of_isFundamentalDomain_of_ae_covers {D' : Set X}
    (hD : IsFundamentalDomain G D μ) (hD' : ∀ᵐ x ∂μ, ∃ g : G, g • x ∈ D') : μ D ≤ μ D' := by
  simpa using setLIntegral_le_of_isFundamentalDomain_of_ae_covers hD hD' (u := fun _ => 1)
    (fun _ _ => rfl)

end Multiplicity

section Subgroup

variable {G X : Type*} [Group G] [MulAction G X] [MeasurableSpace X] {μ : Measure X}
  [MeasurableConstSMul G X] [SMulInvariantMeasure G X μ] [Countable G] {D D' : Set X}
  {K : Subgroup G}

omit [Countable G] [MeasurableConstSMul G X] [SMulInvariantMeasure G X μ] in

@[to_additive  ]
theorem pairwise_aedisjoint_out_inv_smul (hD : IsFundamentalDomain G D μ) (K : Subgroup G) :
    Pairwise (Function.onFun (AEDisjoint μ) fun q : G ⧸ K => (q.out)⁻¹ • D) := by
  intro q₁ q₂ h
  refine hD.aedisjoint fun h' => h ?_
  rw [← q₁.out_eq, ← q₂.out_eq, inv_injective h']

@[to_additive isAddFundamentalDomain_iUnion_out_neg_vadd
]
theorem isFundamentalDomain_iUnion_out_inv_smul (hD : IsFundamentalDomain G D μ)
    (K : Subgroup G) : IsFundamentalDomain K (⋃ q : G ⧸ K, (q.out)⁻¹ • D) μ where
  nullMeasurableSet := by
    have : Countable (G ⧸ K) := QuotientGroup.mk_surjective.countable
    exact .iUnion fun q => hD.nullMeasurableSet_smul _
  ae_covers := by
    filter_upwards [hD.ae_covers] with x ⟨g, hg⟩
    have hk : ((g : G ⧸ K).out)⁻¹ * g ∈ K := QuotientGroup.eq.1 (QuotientGroup.out_eq' _)
    refine ⟨⟨_, hk⟩, mem_iUnion.2 ⟨(g : G ⧸ K), g • x, hg, ?_⟩⟩
    simp [Subgroup.smul_def, smul_smul]
  aedisjoint := by
    have : Countable (G ⧸ K) := QuotientGroup.mk_surjective.countable
    intro k₁ k₂ hk
    simp only [Function.onFun, Subgroup.smul_def, smul_set_iUnion, smul_smul]
    refine AEDisjoint.iUnion_left_iff.2 fun q₁ => AEDisjoint.iUnion_right_iff.2 fun q₂ => ?_
    refine hD.aedisjoint fun h => hk ?_
    have hq : q₁ = q₂ := by
      rw [← q₁.out_eq, ← q₂.out_eq]
      refine QuotientGroup.eq.2 ?_
      have : (q₁.out)⁻¹ * q₂.out = (k₁ : G)⁻¹ * k₂ := by
        rw [eq_inv_mul_iff_mul_eq, ← mul_assoc, h, inv_mul_cancel_right]
      rw [this]
      exact K.mul_mem (K.inv_mem k₁.2) k₂.2
    subst hq
    exact Subtype.ext (mul_right_cancel h)

@[to_additive
]
theorem setLIntegral_subgroup_eq_tsum (hD : IsFundamentalDomain G D μ)
    (hD' : IsFundamentalDomain K D' μ) {u : X → ℝ≥0∞}
    (hu : ∀ (g : G) (x : X), u (g • x) = u x) :
    ∫⁻ x in D', u x ∂μ = ∑' _ : G ⧸ K, ∫⁻ x in D, u x ∂μ := by
  have : Countable (G ⧸ K) := QuotientGroup.mk_surjective.countable
  rw [hD'.setLIntegral_eq (isFundamentalDomain_iUnion_out_inv_smul hD K) u fun k x => hu k x,
    lintegral_iUnion₀ (fun q => hD.nullMeasurableSet_smul _)
      (pairwise_aedisjoint_out_inv_smul hD K)]
  exact tsum_congr fun q => (hD.smul _).setLIntegral_eq hD u hu

@[to_additive setLIntegral_addSubgroup_eq_index_mul
]
theorem setLIntegral_subgroup_eq_index_mul [K.FiniteIndex] (hD : IsFundamentalDomain G D μ)
    (hD' : IsFundamentalDomain K D' μ) {u : X → ℝ≥0∞}
    (hu : ∀ (g : G) (x : X), u (g • x) = u x) :
    ∫⁻ x in D', u x ∂μ = (K.index : ℝ≥0∞) * ∫⁻ x in D, u x ∂μ := by
  have := Fintype.ofFinite (G ⧸ K)
  rw [setLIntegral_subgroup_eq_tsum hD hD' hu, tsum_fintype, Finset.sum_const, nsmul_eq_mul,
    Subgroup.index, Nat.card_eq_fintype_card, Finset.card_univ]

@[to_additive measure_addSubgroup_eq_index_mul
]
theorem measure_subgroup_eq_index_mul [K.FiniteIndex] (hD : IsFundamentalDomain G D μ)
    (hD' : IsFundamentalDomain K D' μ) : μ D' = (K.index : ℝ≥0∞) * μ D := by
  simpa using setLIntegral_subgroup_eq_index_mul hD hD' (u := fun _ => 1) (fun _ _ => rfl)

@[to_additive
]
theorem setLAverage_subgroup_eq [K.FiniteIndex] (hD : IsFundamentalDomain G D μ)
    (hD' : IsFundamentalDomain K D' μ) {u : X → ℝ≥0∞}
    (hu : ∀ (g : G) (x : X), u (g • x) = u x) :
    ⨍⁻ x in D', u x ∂μ = ⨍⁻ x in D, u x ∂μ := by
  rw [setLAverage_eq, setLAverage_eq, setLIntegral_subgroup_eq_index_mul hD hD' hu,
    measure_subgroup_eq_index_mul hD hD', ENNReal.mul_div_mul_left]
  · exact_mod_cast Subgroup.FiniteIndex.index_ne_zero
  · exact ENNReal.natCast_ne_top _

@[to_additive
]
theorem measure_le_measure_subgroup (hD : IsFundamentalDomain G D μ)
    (hD' : IsFundamentalDomain K D' μ) : μ D ≤ μ D' :=
  measure_le_of_isFundamentalDomain_of_ae_covers hD
    (hD'.ae_covers.mono fun _ ⟨k, hk⟩ => ⟨k, hk⟩)

variable {E : Type*} [NormedAddCommGroup E]

@[to_additive
]
theorem integrableOn_subgroup_iff [K.FiniteIndex] (hD : IsFundamentalDomain G D μ)
    (hD' : IsFundamentalDomain K D' μ) {f : X → E}
    (hf : ∀ (g : G) (x : X), f (g • x) = f x) : IntegrableOn f D' μ ↔ IntegrableOn f D μ := by
  rw [hD'.integrableOn_iff (isFundamentalDomain_iUnion_out_inv_smul hD K) fun k x => hf k x,
    integrableOn_finite_iUnion]
  simp only [fun g : G => (hD.smul g).integrableOn_iff hD hf, forall_const]

variable [NormedSpace ℝ E]

@[to_additive setIntegral_addSubgroup_eq_index_smul
]
theorem setIntegral_subgroup_eq_index_smul [K.FiniteIndex] (hD : IsFundamentalDomain G D μ)
    (hD' : IsFundamentalDomain K D' μ) {f : X → E}
    (hf : ∀ (g : G) (x : X), f (g • x) = f x) :
    ∫ x in D', f x ∂μ = (K.index : ℝ) • ∫ x in D, f x ∂μ := by
  by_cases hi : IntegrableOn f D μ
  · have := Fintype.ofFinite (G ⧸ K)
    have hE := isFundamentalDomain_iUnion_out_inv_smul hD K
    rw [hD'.setIntegral_eq hE fun k x => hf k x,
      integral_iUnion_ae (fun q => hD.nullMeasurableSet_smul _)
        (pairwise_aedisjoint_out_inv_smul hD K) ((integrableOn_subgroup_iff hD hE hf).2 hi)]
    simp only [fun g : G => (hD.smul g).setIntegral_eq hD hf]
    rw [tsum_fintype, Finset.sum_const, Subgroup.index, Nat.card_eq_fintype_card,
      Finset.card_univ, Nat.cast_smul_eq_nsmul]
  · rw [integral_undef hi, integral_undef (mt (integrableOn_subgroup_iff hD hD' hf).1 hi),
      smul_zero]

@[to_additive
]
theorem setAverage_subgroup_eq [K.FiniteIndex] (hD : IsFundamentalDomain G D μ)
    (hD' : IsFundamentalDomain K D' μ) {f : X → E}
    (hf : ∀ (g : G) (x : X), f (g • x) = f x) :
    ⨍ x in D', f x ∂μ = ⨍ x in D, f x ∂μ := by
  have h0 : (K.index : ℝ) ≠ 0 := by exact_mod_cast Subgroup.FiniteIndex.index_ne_zero
  rw [setAverage_eq, setAverage_eq, setIntegral_subgroup_eq_index_smul hD hD' hf, smul_smul,
    measureReal_def, measureReal_def, measure_subgroup_eq_index_mul hD hD', ENNReal.toReal_mul,
    ENNReal.toReal_natCast, mul_inv, mul_right_comm, inv_mul_cancel₀ h0, one_mul]

end Subgroup

section Kernel

variable {G H X : Type*} [Group G] [Group H] [MulAction G X] [MulAction H X] [MeasurableSpace X]
  {μ : Measure X} {B D D' : Set X} {φ : G →* H}

@[to_additive  ]
theorem measurableConstSMul_of_surjective [MeasurableConstSMul G X]
    (hφ : Function.Surjective φ) (hφs : ∀ (g : G) (x : X), φ g • x = g • x) :
    MeasurableConstSMul H X where
  measurable_const_smul h := by
    obtain ⟨g, rfl⟩ := hφ h
    simpa only [hφs] using measurable_const_smul g

@[to_additive  ]
theorem smulInvariantMeasure_of_surjective [SMulInvariantMeasure G X μ]
    (hφ : Function.Surjective φ) (hφs : ∀ (g : G) (x : X), φ g • x = g • x) :
    SMulInvariantMeasure H X μ where
  measure_preimage_smul h s hs := by
    obtain ⟨g, rfl⟩ := hφ h
    simpa only [hφs] using SMulInvariantMeasure.measure_preimage_smul g hs

@[to_additive  ]
theorem ae_exists_smul_mem_of_surjective (hφ : Function.Surjective φ)
    (hφs : ∀ (g : G) (x : X), φ g • x = g • x) (hD : IsFundamentalDomain H D μ) :
    ∀ᵐ x ∂μ, ∃ g : G, g • x ∈ D := by
  filter_upwards [hD.ae_covers] with x ⟨h, hh⟩
  obtain ⟨g, rfl⟩ := hφ h
  exact ⟨g, hφs g x ▸ hh⟩

variable [MeasurableConstSMul G X] [SMulInvariantMeasure G X μ] [Countable G]

@[to_additive setLIntegral_le_mul_of_surjective_vadd
]
theorem setLIntegral_le_mul_of_surjective (hφ : Function.Surjective φ)
    (hφs : ∀ (g : G) (x : X), φ g • x = g • x) (hD : IsFundamentalDomain H D μ)
    (hB : NullMeasurableSet B μ) {u : X → ℝ≥0∞} (hu : ∀ (g : G) (x : X), u (g • x) = u x)
    {m : ℝ≥0∞} (hm : ∀ x, ({g : G | g • x ∈ B}.encard : ℝ≥0∞) ≤ m) :
    ∫⁻ x in B, u x ∂μ ≤ m * ∫⁻ x in D, u x ∂μ :=
  setLIntegral_le_mul_of_ae_covers (ae_exists_smul_mem_of_surjective hφ hφs hD) hB hu
    (.of_forall hm)

variable {K : Subgroup G} {H' : Type*} [Group H'] [MulAction H' X] {φ' : K →* H'}

@[to_additive isAddFundamentalDomain_map_of_surjective
]
theorem isFundamentalDomain_map_of_surjective (hφ : Function.Surjective φ)
    (hφs : ∀ (g : G) (x : X), φ g • x = g • x) (hD : IsFundamentalDomain H D μ)
    (hφ' : Function.Surjective φ') (hφs' : ∀ (k : K) (x : X), φ' k • x = k • x)
    (hD' : IsFundamentalDomain H' D' μ) : IsFundamentalDomain (K.map φ) D' μ where
  nullMeasurableSet := hD'.nullMeasurableSet
  ae_covers := by
    filter_upwards [ae_exists_smul_mem_of_surjective hφ' hφs' hD'] with x ⟨k, hk⟩
    refine ⟨⟨φ k, k, k.2, rfl⟩, ?_⟩
    rw [Subgroup.smul_def, hφs]
    exact hk
  aedisjoint := by
    have := measurableConstSMul_of_surjective hφ hφs
    have : SMulInvariantMeasure H X μ := smulInvariantMeasure_of_surjective hφ hφs
    have : Countable H := hφ.countable
    rintro ⟨_, k₁, hk₁, rfl⟩ ⟨_, k₂, hk₂, rfl⟩ hne
    have hne' : φ k₁ ≠ φ k₂ := fun h => hne (Subtype.ext h)
    have hset : ∀ (k : K) (S : Set X), φ k • S = φ' k • S := fun k S => by
      simp only [← image_smul, hφs, hφs', Subgroup.smul_def]
    by_cases hμ : μ = 0
    · simp [hμ, Function.onFun, AEDisjoint]
    have hne'' : φ' ⟨k₁, hk₁⟩ ≠ φ' ⟨k₂, hk₂⟩ := by
      intro h
      have h1 := hD.aedisjoint hne'
      have h2 : φ k₁ • D = φ k₂ • D := by
        rw [hset ⟨k₁, hk₁⟩, hset ⟨k₂, hk₂⟩, h]
      simp only [Function.onFun, AEDisjoint, h2, inter_self, measure_smul] at h1
      exact hD.measure_ne_zero hμ h1
    have h3 := hD'.aedisjoint hne''
    simp only [Function.onFun, ← hset] at h3
    exact h3

omit [MeasurableSpace X] [MulAction G X] [MulAction H X] [MeasurableConstSMul G X]
  [SMulInvariantMeasure G X μ] [Countable G] in

@[to_additive finiteIndex_addSubgroup_map_of_surjective
]
theorem finiteIndex_map_of_surjective [K.FiniteIndex] (hφ : Function.Surjective φ) :
    (K.map φ).FiniteIndex :=
  ⟨ne_zero_of_dvd_ne_zero Subgroup.FiniteIndex.index_ne_zero (K.index_map_dvd hφ)⟩

@[to_additive setLIntegral_eq_index_map_mul_vadd
]
theorem setLIntegral_eq_index_map_mul [K.FiniteIndex] (hφ : Function.Surjective φ)
    (hφs : ∀ (g : G) (x : X), φ g • x = g • x) (hD : IsFundamentalDomain H D μ)
    (hφ' : Function.Surjective φ') (hφs' : ∀ (k : K) (x : X), φ' k • x = k • x)
    (hD' : IsFundamentalDomain H' D' μ) {u : X → ℝ≥0∞}
    (hu : ∀ (g : G) (x : X), u (g • x) = u x) :
    ∫⁻ x in D', u x ∂μ = ((K.map φ).index : ℝ≥0∞) * ∫⁻ x in D, u x ∂μ := by
  have := measurableConstSMul_of_surjective hφ hφs
  have : SMulInvariantMeasure H X μ := smulInvariantMeasure_of_surjective hφ hφs
  have : Countable H := hφ.countable
  have := finiteIndex_map_of_surjective (K := K) hφ
  refine setLIntegral_subgroup_eq_index_mul hD
    (isFundamentalDomain_map_of_surjective hφ hφs hD hφ' hφs' hD') fun h x => ?_
  obtain ⟨g, rfl⟩ := hφ h
  rw [hφs, hu]

@[to_additive measure_eq_index_map_mul_vadd
]
theorem measure_eq_index_map_mul [K.FiniteIndex] (hφ : Function.Surjective φ)
    (hφs : ∀ (g : G) (x : X), φ g • x = g • x) (hD : IsFundamentalDomain H D μ)
    (hφ' : Function.Surjective φ') (hφs' : ∀ (k : K) (x : X), φ' k • x = k • x)
    (hD' : IsFundamentalDomain H' D' μ) : μ D' = ((K.map φ).index : ℝ≥0∞) * μ D := by
  simpa using setLIntegral_eq_index_map_mul hφ hφs hD hφ' hφs' hD' (u := fun _ => 1)
    (fun _ _ => rfl)

@[to_additive setLAverage_eq_of_surjective_vadd
]
theorem setLAverage_eq_of_surjective [K.FiniteIndex] (hφ : Function.Surjective φ)
    (hφs : ∀ (g : G) (x : X), φ g • x = g • x) (hD : IsFundamentalDomain H D μ)
    (hφ' : Function.Surjective φ') (hφs' : ∀ (k : K) (x : X), φ' k • x = k • x)
    (hD' : IsFundamentalDomain H' D' μ) {u : X → ℝ≥0∞}
    (hu : ∀ (g : G) (x : X), u (g • x) = u x) :
    ⨍⁻ x in D', u x ∂μ = ⨍⁻ x in D, u x ∂μ := by
  have := finiteIndex_map_of_surjective (K := K) hφ
  rw [setLAverage_eq, setLAverage_eq, setLIntegral_eq_index_map_mul hφ hφs hD hφ' hφs' hD' hu,
    measure_eq_index_map_mul hφ hφs hD hφ' hφs' hD', ENNReal.mul_div_mul_left]
  · exact_mod_cast Subgroup.FiniteIndex.index_ne_zero
  · exact ENNReal.natCast_ne_top _

@[to_additive measure_le_measure_of_surjective_vadd
]
theorem measure_le_measure_of_surjective (hφ : Function.Surjective φ)
    (hφs : ∀ (g : G) (x : X), φ g • x = g • x) (hD : IsFundamentalDomain H D μ)
    (hφ' : Function.Surjective φ') (hφs' : ∀ (k : K) (x : X), φ' k • x = k • x)
    (hD' : IsFundamentalDomain H' D' μ) : μ D ≤ μ D' := by
  have := measurableConstSMul_of_surjective hφ hφs
  have : SMulInvariantMeasure H X μ := smulInvariantMeasure_of_surjective hφ hφs
  have : Countable H := hφ.countable
  exact measure_le_measure_subgroup hD
    (isFundamentalDomain_map_of_surjective hφ hφs hD hφ' hφs' hD')

@[to_additive setAverage_eq_of_surjective_vadd
]
theorem setAverage_eq_of_surjective [K.FiniteIndex] (hφ : Function.Surjective φ)
    (hφs : ∀ (g : G) (x : X), φ g • x = g • x) (hD : IsFundamentalDomain H D μ)
    (hφ' : Function.Surjective φ') (hφs' : ∀ (k : K) (x : X), φ' k • x = k • x)
    (hD' : IsFundamentalDomain H' D' μ) {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : X → E} (hf : ∀ (g : G) (x : X), f (g • x) = f x) :
    (IntegrableOn f D' μ ↔ IntegrableOn f D μ) ∧
      ∫ x in D', f x ∂μ = ((K.map φ).index : ℝ) • ∫ x in D, f x ∂μ ∧
      ⨍ x in D', f x ∂μ = ⨍ x in D, f x ∂μ := by
  have := measurableConstSMul_of_surjective hφ hφs
  have : SMulInvariantMeasure H X μ := smulInvariantMeasure_of_surjective hφ hφs
  have : Countable H := hφ.countable
  have := finiteIndex_map_of_surjective (K := K) hφ
  have hD'' := isFundamentalDomain_map_of_surjective hφ hφs hD hφ' hφs' hD'
  have hf' : ∀ (h : H) (x : X), f (h • x) = f x := fun h x => by
    obtain ⟨g, rfl⟩ := hφ h
    rw [hφs, hf]
  exact ⟨integrableOn_subgroup_iff hD hD'' hf', setIntegral_subgroup_eq_index_smul hD hD'' hf',
    setAverage_subgroup_eq hD hD'' hf'⟩

theorem unfolding_isFundamentalDomain (hφ : Function.Surjective φ)
    (hφs : ∀ (g : G) (x : X), φ g • x = g • x) (hD : IsFundamentalDomain H D μ)
    {u : X → ℝ≥0∞} (hu : ∀ (g : G) (x : X), u (g • x) = u x) :
    (∀ B : Set X, NullMeasurableSet B μ → ∀ m : ℝ≥0∞,
      (∀ x, ({g : G | g • x ∈ B}.encard : ℝ≥0∞) ≤ m) →
        ∫⁻ x in B, u x ∂μ ≤ m * ∫⁻ x in D, u x ∂μ) ∧
    (∀ B : Set X, NullMeasurableSet B μ → ∫⁻ x in B, u x ∂μ
      ≤ ({g : G | (g • B ∩ B).Nonempty}.encard : ℝ≥0∞) * ∫⁻ x in D, u x ∂μ) ∧
    (Function.Surjective φ' → (∀ (k : K) (x : X), φ' k • x = k • x) →
      IsFundamentalDomain H' D' μ →
        μ D ≤ μ D' ∧ (K.FiniteIndex →
          (∃ n : ℕ, 0 < n ∧ n ∣ K.index ∧ μ D' = n * μ D ∧
            ∫⁻ x in D', u x ∂μ = n * ∫⁻ x in D, u x ∂μ) ∧
          ⨍⁻ x in D', u x ∂μ = ⨍⁻ x in D, u x ∂μ)) := by
  refine ⟨fun B hB m hm => setLIntegral_le_mul_of_surjective hφ hφs hD hB hu hm,
    fun B hB => setLIntegral_le_encard_mul_of_ae_covers
      (ae_exists_smul_mem_of_surjective hφ hφs hD) hB hu,
    fun hφ' hφs' hD' => ⟨measure_le_measure_of_surjective hφ hφs hD hφ' hφs' hD', fun _ =>
      ⟨⟨(K.map φ).index, ?_, K.index_map_dvd hφ, measure_eq_index_map_mul hφ hφs hD hφ' hφs' hD',
        setLIntegral_eq_index_map_mul hφ hφs hD hφ' hφs' hD' hu⟩,
        setLAverage_eq_of_surjective hφ hφs hD hφ' hφs' hD' hu⟩⟩⟩
  exact Nat.pos_of_ne_zero (finiteIndex_map_of_surjective (K := K) hφ).index_ne_zero

end Kernel

section Image

variable {G X : Type*} [Group G] [MulAction G X] [MeasurableSpace X] {μ : Measure X}
  [MeasurableConstSMul G X] [SMulInvariantMeasure G X μ] [Countable G] {B D D' : Set X}
  {K : Subgroup G}

theorem setLIntegral_le_mul_of_range_toPermHom
    (hD : IsFundamentalDomain (MulAction.toPermHom G X).range D μ)
    (hB : NullMeasurableSet B μ) {u : X → ℝ≥0∞} (hu : ∀ (g : G) (x : X), u (g • x) = u x)
    {m : ℝ≥0∞} (hm : ∀ x, ({g : G | g • x ∈ B}.encard : ℝ≥0∞) ≤ m) :
    ∫⁻ x in B, u x ∂μ ≤ m * ∫⁻ x in D, u x ∂μ :=
  setLIntegral_le_mul_of_surjective (MulAction.toPermHom G X).rangeRestrict_surjective
    (fun _ _ => rfl) hD hB hu hm

theorem measure_le_measure_of_range_toPermHom
    (hD : IsFundamentalDomain (MulAction.toPermHom G X).range D μ)
    (hD' : IsFundamentalDomain (MulAction.toPermHom K X).range D' μ) : μ D ≤ μ D' :=
  measure_le_measure_of_surjective (MulAction.toPermHom G X).rangeRestrict_surjective
    (fun _ _ => rfl) hD (MulAction.toPermHom K X).rangeRestrict_surjective (fun _ _ => rfl) hD'

theorem setLAverage_eq_of_range_toPermHom [K.FiniteIndex]
    (hD : IsFundamentalDomain (MulAction.toPermHom G X).range D μ)
    (hD' : IsFundamentalDomain (MulAction.toPermHom K X).range D' μ) {u : X → ℝ≥0∞}
    (hu : ∀ (g : G) (x : X), u (g • x) = u x) :
    ⨍⁻ x in D', u x ∂μ = ⨍⁻ x in D, u x ∂μ :=
  setLAverage_eq_of_surjective (MulAction.toPermHom G X).rangeRestrict_surjective
    (fun _ _ => rfl) hD (MulAction.toPermHom K X).rangeRestrict_surjective (fun _ _ => rfl) hD' hu

end Image

end GlobalTheory
