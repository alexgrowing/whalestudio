import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMulRightInvariantSemi

open MeasureTheory GlobalTheory.Unf.SemiFd GlobalTheory.SemiMean
open scoped Pointwise ENNReal

noncomputable section

namespace GlobalTheory.SemiUnfold

theorem isFundamentalDomain_iUnion {P ι : Type} [Group P] [MeasurableSpace P] [MeasurableMul P] [Countable ι]
    (μ : Measure P) [μ.IsMulLeftInvariant] (Γ₀ Γ : Subgroup P) [Countable Γ] (hle : Γ₀ ≤ Γ) (r : ι → Γ)
    (hsurj : ∀ γ ∈ Γ, ∃ δ ∈ Γ₀, ∃ i, γ = δ * r i)
    (hinj : ∀ δ ∈ Γ₀, ∀ δ' ∈ Γ₀, ∀ i j, δ * r i = δ' * r j → δ = δ' ∧ i = j)
    (𝓕 : Set P) (h : IsFundamentalDomain Γ 𝓕 μ) : IsFundamentalDomain Γ₀ (⋃ i, r i • 𝓕) μ := by
  letI : MeasurableSpace Γ := ⊤
  haveI : MeasurableSMul Γ P :=
    { measurable_const_smul := fun γ => measurable_const_mul (γ : P)
      measurable_smul_const := fun _ => measurable_from_top }
  refine ⟨NullMeasurableSet.iUnion fun i => h.nullMeasurableSet_smul _, ?_, ?_⟩
  · filter_upwards [h.ae_covers] with x ⟨γ, hγ⟩
    obtain ⟨δ, hδ, i, hi⟩ := hsurj γ⁻¹ (inv_mem γ.2)
    refine ⟨⟨δ, hδ⟩⁻¹, Set.mem_iUnion.2 ⟨i, _, hγ, ?_⟩⟩
    have : (r i : P) = δ⁻¹ * (γ : P)⁻¹ := by rw [hi]; group
    simp [Subgroup.smul_def, this, mul_assoc]
  · intro δ δ' hne
    have e : ∀ δ : Γ₀, δ • (⋃ i, r i • 𝓕) = ⋃ i, ((⟨δ.1, hle δ.2⟩ : Γ) * r i) • 𝓕 := fun δ => by
      rw [Set.smul_set_iUnion]
      refine Set.iUnion_congr fun i => ?_
      rw [mul_smul]; rfl
    simp only [Function.onFun, e]
    refine AEDisjoint.iUnion_left_iff.2 fun i => AEDisjoint.iUnion_right_iff.2 fun j => h.aedisjoint fun he => hne ?_
    exact Subtype.ext (hinj _ δ.2 _ δ'.2 i j (congrArg Subtype.val he)).1

theorem unfold_cosets {P ι : Type} [Group P] [MeasurableSpace P] [MeasurableMul P] [Countable ι]
    (μ : Measure P) [μ.IsMulLeftInvariant] (Γ₀ Γ : Subgroup P) [Countable Γ] (hle : Γ₀ ≤ Γ) (r : ι → Γ)
    (hsurj : ∀ γ ∈ Γ, ∃ δ ∈ Γ₀, ∃ i, γ = δ * r i)
    (hinj : ∀ δ ∈ Γ₀, ∀ δ' ∈ Γ₀, ∀ i j, δ * r i = δ' * r j → δ = δ' ∧ i = j)
    (𝓕 : Set P) (h : IsFundamentalDomain Γ 𝓕 μ) (hfin : μ 𝓕 ≠ ∞) (𝓓 : Set P) (h₀ : IsFundamentalDomain Γ₀ 𝓓 μ)
    (φ : P → ℂ) (hφ : Measurable φ) (hφi : ∀ δ ∈ Γ₀, ∀ x, φ (δ * x) = φ x) (C : ℝ)
    (hC : ∀ x, Summable (fun i => ‖φ (r i * x)‖) ∧ ∑' i, ‖φ (r i * x)‖ ≤ C) :
    IntegrableOn φ 𝓓 μ ∧ ∫ x in 𝓕, ∑' i, φ (r i * x) ∂μ = ∫ x in 𝓓, φ x ∂μ := by
  letI : MeasurableSpace Γ := ⊤
  haveI : MeasurableSMul Γ P :=
    { measurable_const_smul := fun γ => measurable_const_mul (γ : P)
      measurable_smul_const := fun _ => measurable_from_top }
  letI : MeasurableSpace Γ₀ := ⊤
  haveI : MeasurableSMul Γ₀ P :=
    { measurable_const_smul := fun γ => measurable_const_mul (γ : P)
      measurable_smul_const := fun _ => measurable_from_top }
  haveI : Countable Γ₀ := (Subgroup.inclusion_injective hle).countable
  have hU := isFundamentalDomain_iUnion μ Γ₀ Γ hle r hsurj hinj 𝓕 h
  have hd : Pairwise (Function.onFun (AEDisjoint μ) fun i => r i • 𝓕) := fun i j hij =>
    h.aedisjoint fun he => hij (hinj 1 (one_mem _) 1 (one_mem _) i j (by rw [he])).2
  have hm : ∀ i, NullMeasurableSet (r i • 𝓕) μ := fun i => h.nullMeasurableSet_smul _
  have hmi : ∀ i, Measurable fun x => φ (r i * x) := fun i => hφ.comp (measurable_const_mul _)
  have hpre : ∀ i, (fun x => (r i : P) * x) ⁻¹' (r i • 𝓕) = 𝓕 := fun i =>
    Set.ext fun x => Set.smul_mem_smul_set_iff (a := r i)
  have hl : ∑' i, ∫⁻ x in 𝓕, ‖φ (r i * x)‖ₑ ∂μ ≠ ∞ := by
    rw [← lintegral_tsum fun i => (hmi i).enorm.aemeasurable]
    refine ne_of_lt (lt_of_le_of_lt (lintegral_mono (g := fun _ => ENNReal.ofReal C) fun x => ?_) ?_)
    · simp only [← ofReal_norm_eq_enorm]
      rw [← ENNReal.ofReal_tsum_of_nonneg (fun _ => norm_nonneg _) (hC x).1]
      exact ENNReal.ofReal_le_ofReal (hC x).2
    · rw [lintegral_const, Measure.restrict_apply_univ]
      exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top hfin.lt_top
  have hI : IntegrableOn φ (⋃ i, r i • 𝓕) μ := by
    refine ⟨hφ.aestronglyMeasurable, ?_⟩
    rw [HasFiniteIntegral, lintegral_iUnion₀ hm hd]
    refine lt_of_eq_of_lt (tsum_congr fun i => ?_) hl.lt_top
    rw [← (measurePreserving_mul_left μ (r i : P)).setLIntegral_comp_preimage_emb (measurableEmbedding_mulLeft _), hpre]
  have hinv : ∀ (δ : Γ₀) x, φ (δ • x) = φ x := fun δ x => hφi δ δ.2 x
  refine ⟨(hU.integrableOn_iff h₀ hinv).1 hI, ?_⟩
  rw [← hU.setIntegral_eq h₀ hinv, integral_iUnion_ae hm hd hI, integral_tsum (fun i => (hmi i).aestronglyMeasurable) hl]
  refine tsum_congr fun i => ?_
  rw [← (measurePreserving_mul_left μ (r i : P)).setIntegral_preimage_emb (measurableEmbedding_mulLeft _) φ, hpre]

variable {G K : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
  [Group K] [TopologicalSpace K] [IsTopologicalGroup K] [LocallyCompactSpace K]
  [SecondCountableTopology K] [T2Space K] [MeasurableSpace K] [BorelSpace K]

theorem cocompact_of_semi (Γ N : Subgroup G) [DiscreteTopology Γ] (hN : IsClosed (N : Set G)) (s : K →* G)
    (hs : Continuous s) (hc : ∀ n ∈ N, ∀ h, s h * n * (s h)⁻¹ ∈ N)
    (hinj : ∀ n ∈ N, ∀ n' ∈ N, ∀ h h', n * s h = n' * s h' → n = n' ∧ h = h')
    (ΓK : Subgroup K) (hrat : ∀ n ∈ N, ∀ h, n * s h ∈ Γ ↔ n ∈ Γ ∧ h ∈ ΓK)
    (hP : ∃ C : Set (N ⊔ s.range : Subgroup G), IsCompact C ∧ ∀ n : (N ⊔ s.range : Subgroup G),
      ∃ γ ∈ Γ.subgroupOf (N ⊔ s.range), γ * n ∈ C) :
    ∃ C : Set N, IsCompact C ∧ ∀ n : N, ∃ γ ∈ Γ.subgroupOf N, γ * n ∈ C := by
  haveI : LocallyCompactSpace N := hN.locallyCompactSpace
  haveI : SecondCountableTopology N := TopologicalSpace.Subtype.secondCountableTopology _
  haveI : LocallyCompactSpace (N ⊔ s.range : Subgroup G) := (isClosed_of_cocompact Γ _ hP).locallyCompactSpace
  have hr : ∀ h ∈ ΓK, s h ∈ Γ := fun g hg => by simpa using (hrat 1 (one_mem _) g).2 ⟨one_mem _, hg⟩
  letI act : MulAction (N × K) (N ⊔ s.range : Subgroup G) :=
    { smul := fun p x => ⟨p.1 * x * (s p.2)⁻¹, mul_mem (mul_mem (Subgroup.mem_sup_left p.1.2) x.2)
        (inv_mem (Subgroup.mem_sup_right ⟨p.2, rfl⟩))⟩
      one_smul := fun x => Subtype.ext (show ((1 : N) : G) * x * (s 1)⁻¹ = x by simp)
      mul_smul := fun p q x => Subtype.ext
        (show ((p.1 * q.1 : N) : G) * x * (s (p.2 * q.2))⁻¹ = p.1 * (q.1 * x * (s q.2)⁻¹) * (s p.2)⁻¹ by
          simp [mul_assoc]) }
  have hsm : ∀ (p : N × K) (x : (N ⊔ s.range : Subgroup G)), ((p • x : (N ⊔ s.range : Subgroup G)) : G) =
      p.1 * x * (s p.2)⁻¹ := fun _ _ => rfl
  haveI : ContinuousSMul (N × K) (N ⊔ s.range : Subgroup G) := ⟨Continuous.subtype_mk (by fun_prop) _⟩
  have hsurj : Function.Surjective fun p : N × K => p • (1 : (N ⊔ s.range : Subgroup G)) := fun x => by
    obtain ⟨n, hn, h, hx⟩ := mem_sup_decomp N s hc x.2
    exact ⟨(⟨n, hn⟩, h⁻¹), Subtype.ext (by simp [hsm, hx])⟩
  haveI : MulAction.IsPretransitive (N × K) (N ⊔ s.range : Subgroup G) := ⟨fun x y => by
    obtain ⟨p, rfl⟩ := hsurj x
    obtain ⟨q, rfl⟩ := hsurj y
    exact ⟨q * p⁻¹, by simp [smul_smul]⟩⟩
  have hi : Function.Injective fun p : N × K => p • (1 : (N ⊔ s.range : Subgroup G)) := fun p q he => by
    have h1 := congrArg Subtype.val he
    simp only [hsm, OneMemClass.coe_one, mul_one, ← map_inv] at h1
    obtain ⟨h2, h3⟩ := hinj _ p.1.2 _ q.1.2 _ _ h1
    exact Prod.ext (Subtype.ext h2) (inv_injective h3)
  let e := (Equiv.ofBijective _ ⟨hi, hsurj⟩).toHomeomorphOfContinuousOpen
    (continuous_id.smul continuous_const)
    (isOpenMap_smul_of_sigmaCompact (G := N × K) (1 : (N ⊔ s.range : Subgroup G)))
  obtain ⟨C, hC, hCs⟩ := hP
  let q : N × K → N := fun p => ⟨s p.2 * p.1 * (s p.2)⁻¹, hc _ p.1.2 _⟩
  have hq : Continuous q := Continuous.subtype_mk (by fun_prop) _
  refine ⟨q '' (e ⁻¹' C), (e.isCompact_preimage.2 hC).image hq, fun n => ?_⟩
  obtain ⟨γ, hγ, hk⟩ := hCs ⟨n, Subgroup.mem_sup_left n.2⟩
  obtain ⟨δ, hδ, k, hx⟩ := mem_sup_decomp N s hc γ.2
  obtain ⟨h1, h2⟩ := (hrat δ hδ k).1 (hx ▸ Subgroup.mem_subgroupOf.1 hγ)
  refine ⟨⟨_, hc δ hδ k⁻¹⟩, Subgroup.mem_subgroupOf.2
    (mul_mem (mul_mem (hr _ (inv_mem h2)) h1) (inv_mem (hr _ (inv_mem h2)))),
    (⟨_, mul_mem hδ (hc n n.2 k)⟩, k⁻¹), ?_, Subtype.ext ?_⟩
  · have : e (⟨_, mul_mem hδ (hc n n.2 k)⟩, k⁻¹) = γ * ⟨n, Subgroup.mem_sup_left n.2⟩ := Subtype.ext (by
      show δ * (s k * n * (s k)⁻¹) * 1 * (s k⁻¹)⁻¹ = γ * n
      rw [hx]; simp [mul_assoc])
    show e _ ∈ C
    rwa [this]
  · show s k⁻¹ * (δ * (s k * n * (s k)⁻¹)) * (s k⁻¹)⁻¹ = s k⁻¹ * δ * (s k⁻¹)⁻¹ * n
    simp [mul_assoc]

theorem countable_subgroupOf (Γ P : Subgroup G) [Countable Γ] : Countable (Γ.subgroupOf P) :=
  Function.Injective.countable (f := fun g : Γ.subgroupOf P => (⟨g.1.1, g.2⟩ : Γ))
    fun _ _ hgh => Subtype.ext (Subtype.ext (congrArg Subtype.val hgh :))

theorem map_semiMap_eq (Γ N : Subgroup G) [DiscreteTopology Γ] [Countable Γ] (hN : IsClosed (N : Set G)) (s : K →* G)
    (hs : Continuous s) (hc : ∀ n ∈ N, ∀ h, s h * n * (s h)⁻¹ ∈ N)
    (hinj : ∀ n ∈ N, ∀ n' ∈ N, ∀ h h', n * s h = n' * s h' → n = n' ∧ h = h')
    (ΓK : Subgroup K) [Countable ΓK] (hrat : ∀ n ∈ N, ∀ h, n * s h ∈ Γ ↔ n ∈ Γ ∧ h ∈ ΓK)
    (hP : IsClosed ((N ⊔ s.range : Subgroup G) : Set G))
    (μ : Measure K) [μ.IsHaarMeasure] (𝓕 : Set K) (h𝓕 : IsFundamentalDomain ΓK 𝓕 μ) (h1 : μ 𝓕 = 1)
    (ν : Measure N) [ν.IsHaarMeasure] (𝓝 : Set N) (h𝓝 : IsFundamentalDomain (Γ.subgroupOf N) 𝓝 ν) (k1 : ν 𝓝 = 1)
    (μ' : Measure (N ⊔ s.range : Subgroup G)) (𝓕' : Set (N ⊔ s.range : Subgroup G)) (hμ' : μ'.IsHaarMeasure)
    (h𝓕' : IsFundamentalDomain (Γ.subgroupOf (N ⊔ s.range)) 𝓕' μ') (h1' : μ' 𝓕' = 1) :
    (μ.prod ν).map (semiMap N s) = μ' := by
  haveI : LocallyCompactSpace N := hN.locallyCompactSpace
  haveI : SecondCountableTopology N := TopologicalSpace.Subtype.secondCountableTopology _
  haveI : LocallyCompactSpace (N ⊔ s.range : Subgroup G) := hP.locallyCompactSpace
  haveI : SecondCountableTopology (N ⊔ s.range : Subgroup G) := TopologicalSpace.Subtype.secondCountableTopology _
  haveI := countable_subgroupOf Γ N
  haveI := countable_subgroupOf Γ (N ⊔ s.range)
  have hme := semiMap_me N s hN hs hinj
  have hi := semiMap_injective N s hinj
  haveI : μ.IsMulRightInvariant := GlobalTheory.UnitU.isMulRightInvariant_of_fundamentalDomain ΓK μ h𝓕
    (by rw [h1]; exact one_ne_zero) (by rw [h1]; exact ENNReal.one_ne_top)
  haveI : ν.IsMulRightInvariant := GlobalTheory.UnitU.isMulRightInvariant_of_fundamentalDomain _ ν h𝓝
    (by rw [k1]; exact one_ne_zero) (by rw [k1]; exact ENNReal.one_ne_top)
  have hfd := isFundamentalDomain_semi N s hN hs hc hinj Γ ΓK hrat μ ν 𝓕 𝓝 h𝓕 h𝓝
  rw [semiMeas_eq, Subgroup.inf_subgroupOf_right] at hfd
  have hm1 : (μ.prod ν).map (semiMap N s) (semiMap N s '' (𝓕 ×ˢ 𝓝)) = 1 := by
    rw [hme.map_apply, Set.preimage_image_eq _ hi, Measure.prod_prod, h1, k1, one_mul]
  exact eq_of_rightInvariant _ μ' _ 𝓕' _ hμ' h𝓕' h1' hme.sigmaFinite_map
    (isMulRightInvariant_semi N s hN hs hc μ ν) hfd hm1

theorem mean_factor (Γ N : Subgroup G) [DiscreteTopology Γ] [Countable Γ] (hN : IsClosed (N : Set G)) (s : K →* G)
    (hs : Continuous s) (hc : ∀ n ∈ N, ∀ h, s h * n * (s h)⁻¹ ∈ N)
    (hinj : ∀ n ∈ N, ∀ n' ∈ N, ∀ h h', n * s h = n' * s h' → n = n' ∧ h = h')
    (ΓK : Subgroup K) [Countable ΓK] (hrat : ∀ n ∈ N, ∀ h, n * s h ∈ Γ ↔ n ∈ Γ ∧ h ∈ ΓK)
    (P : Subgroup G) (hPe : P = N ⊔ s.range)
    (hP : ∃ C : Set P, IsCompact C ∧ ∀ n : P, ∃ γ ∈ Γ.subgroupOf P, γ * n ∈ C)
    (μ : Measure K) [μ.IsHaarMeasure] (𝓕 : Set K) (h𝓕 : IsFundamentalDomain ΓK 𝓕 μ) (h1 : μ 𝓕 = 1)
    (μ' : Measure P) (𝓕' : Set P) (hμ' : μ'.IsHaarMeasure)
    (h𝓕' : IsFundamentalDomain (Γ.subgroupOf P) 𝓕' μ') (h1' : μ' 𝓕' = 1)
    (φ : G → ℂ) (ψ : K → ℂ) (hφψ : ∀ n ∈ N, ∀ h, φ (n * s h) = ψ h) (hφi : ∀ γ ∈ Γ, γ ∈ P → ∀ x, φ (γ * x) = φ x) :
    ∫ r in 𝓕', φ r.1 ∂μ' = ∫ h in 𝓕, ψ h ∂μ := by
  subst hPe
  obtain ⟨ν, 𝓝, hν, h𝓝, k1⟩ := exists_mass_one Γ N (cocompact_of_semi Γ N hN s hs hc hinj ΓK hrat hP)
  haveI : LocallyCompactSpace N := hN.locallyCompactSpace
  haveI : SecondCountableTopology N := TopologicalSpace.Subtype.secondCountableTopology _
  haveI := countable_subgroupOf Γ (N ⊔ s.range)
  have hme := semiMap_me N s hN hs hinj
  have hi := semiMap_injective N s hinj
  have he := map_semiMap_eq Γ N hN s hs hc hinj ΓK hrat (isClosed_of_cocompact Γ _ hP) μ 𝓕 h𝓕 h1 ν 𝓝 h𝓝 k1
    μ' 𝓕' hμ' h𝓕' h1'
  have hfd := isFundamentalDomain_semi N s hN hs hc hinj Γ ΓK hrat μ ν 𝓕 𝓝 h𝓕 h𝓝
  rw [semiMeas_eq, Subgroup.inf_subgroupOf_right, he] at hfd
  letI : MeasurableSpace (Γ.subgroupOf (N ⊔ s.range)) := ⊤
  haveI : MeasurableSMul (Γ.subgroupOf (N ⊔ s.range)) (N ⊔ s.range : Subgroup G) :=
    { measurable_const_smul := fun γ => measurable_const_mul (γ : (N ⊔ s.range : Subgroup G))
      measurable_smul_const := fun _ => measurable_from_top }
  rw [h𝓕'.setIntegral_eq hfd (f := fun r => φ r.1) (fun γ x => hφi _ (Subgroup.mem_subgroupOf.1 γ.2) γ.1.2 _), ← he,
    hme.restrict_map, Set.preimage_image_eq _ hi, ← Measure.prod_restrict, hme.integral_map]
  have : (fun p : K × N => φ (semiMap N s p).1) = fun p => ψ p.1 := funext fun p => hφψ _ p.2.2 _
  rw [this, integral_fun_fst, Measure.real, Measure.restrict_apply_univ, k1]
  simp

theorem unfold_semi (Γ N : Subgroup G) [DiscreteTopology Γ] [Countable Γ] (hN : IsClosed (N : Set G)) (s : K →* G)
    (hs : Continuous s) (hc : ∀ n ∈ N, ∀ h, s h * n * (s h)⁻¹ ∈ N)
    (hinj : ∀ n ∈ N, ∀ n' ∈ N, ∀ h h', n * s h = n' * s h' → n = n' ∧ h = h')
    (ΓK : Subgroup K) [Countable ΓK] (hrat : ∀ n ∈ N, ∀ h, n * s h ∈ Γ ↔ n ∈ Γ ∧ h ∈ ΓK)
    (P : Subgroup G) (hPe : P = N ⊔ s.range) (hP : IsClosed (P : Set G))
    (μ : Measure K) [μ.IsHaarMeasure] (𝓕 : Set K) (h𝓕 : IsFundamentalDomain ΓK 𝓕 μ) (h1 : μ 𝓕 = 1)
    (ν : Measure N) [ν.IsHaarMeasure] (𝓝 : Set N) (h𝓝 : IsFundamentalDomain (Γ.subgroupOf N) 𝓝 ν) (k1 : ν 𝓝 = 1)
    (μ' : Measure P) (𝓕' : Set P) (hμ' : μ'.IsHaarMeasure)
    (h𝓕' : IsFundamentalDomain (Γ.subgroupOf P) 𝓕' μ') (h1' : μ' 𝓕' = 1)
    (φ : G → ℂ) (hφ : Measurable φ) (hφi : ∀ γ ∈ Γ, γ ∈ N → ∀ x, φ (γ * x) = φ x) (C : ℝ)
    (hC : ∀ x ∈ P, Summable (fun k : ΓK => ‖φ (s k * x)‖) ∧ ∑' k : ΓK, ‖φ (s k * x)‖ ≤ C) :
    Integrable (fun h => ∫ n in 𝓝, φ (n.1 * s h) ∂ν) μ ∧
      ∫ r in 𝓕', ∑' k : ΓK, φ (s k * r.1) ∂μ' = ∫ h, ∫ n in 𝓝, φ (n.1 * s h) ∂ν ∂μ := by
  subst hPe
  haveI : LocallyCompactSpace N := hN.locallyCompactSpace
  haveI : SecondCountableTopology N := TopologicalSpace.Subtype.secondCountableTopology _
  haveI : SecondCountableTopology (N ⊔ s.range : Subgroup G) := TopologicalSpace.Subtype.secondCountableTopology _
  haveI := countable_subgroupOf Γ (N ⊔ s.range)
  have hme := semiMap_me N s hN hs hinj
  have hi := semiMap_injective N s hinj
  have hr : ∀ h ∈ ΓK, s h ∈ Γ := fun g hg => by simpa using (hrat 1 (one_mem _) g).2 ⟨one_mem _, hg⟩
  have he := map_semiMap_eq Γ N hN s hs hc hinj ΓK hrat hP μ 𝓕 h𝓕 h1 ν 𝓝 h𝓝 k1 μ' 𝓕' hμ' h𝓕' h1'
  have hu : IsFundamentalDomain (⊥ : Subgroup K) Set.univ μ :=
    IsFundamentalDomain.mk' MeasurableSet.univ.nullMeasurableSet fun _ =>
      ⟨1, Set.mem_univ _, fun _ _ => Subsingleton.elim _ _⟩
  have h𝓝' : IsFundamentalDomain ((Γ ⊓ N).subgroupOf N) 𝓝 ν := by rwa [Subgroup.inf_subgroupOf_right]
  have hfd := isFundamentalDomain_semi N s hN hs hc hinj (Γ ⊓ N) ⊥ (fun n hn h => ⟨fun hm => by
      obtain ⟨h2, h3⟩ := hinj n hn _ (Subgroup.mem_inf.1 hm).2 h 1 (by simp)
      exact ⟨h2 ▸ hm, Subgroup.mem_bot.2 h3⟩,
    fun hm => by rw [Subgroup.mem_bot.1 hm.2, map_one, mul_one]; exact hm.1⟩) μ ν Set.univ 𝓝 hu h𝓝'
  rw [semiMeas_eq, Subgroup.inf_subgroupOf_right, he] at hfd
  obtain ⟨hI, hE⟩ := unfold_cosets μ' ((Γ ⊓ N).subgroupOf (N ⊔ s.range)) (Γ.subgroupOf (N ⊔ s.range))
    (fun x hx => Subgroup.mem_subgroupOf.2 (Subgroup.mem_inf.1 (Subgroup.mem_subgroupOf.1 hx)).1)
    (fun k : ΓK => ⟨⟨s k, Subgroup.mem_sup_right ⟨k, rfl⟩⟩, Subgroup.mem_subgroupOf.2 (hr _ k.2)⟩)
    (fun γ hγ => by
      obtain ⟨δ, hδ, k, hx⟩ := mem_sup_decomp N s hc γ.2
      obtain ⟨h2, h3⟩ := (hrat δ hδ k).1 (hx ▸ Subgroup.mem_subgroupOf.1 hγ)
      exact ⟨⟨δ, Subgroup.mem_sup_left hδ⟩, Subgroup.mem_subgroupOf.2 (Subgroup.mem_inf.2 ⟨h2, hδ⟩), ⟨k, h3⟩,
        Subtype.ext hx⟩)
    (fun δ hδ δ' hδ' i j hij => by
      obtain ⟨h2, h3⟩ := hinj _ (Subgroup.mem_inf.1 (Subgroup.mem_subgroupOf.1 hδ)).2 _
        (Subgroup.mem_inf.1 (Subgroup.mem_subgroupOf.1 hδ')).2 _ _ (congrArg Subtype.val hij)
      exact ⟨Subtype.ext h2, Subtype.ext h3⟩)
    𝓕' h𝓕' (by rw [h1']; exact ENNReal.one_ne_top) _ hfd (fun r => φ r.1) (hφ.comp measurable_subtype_coe)
    (fun δ hδ x => hφi _ (Subgroup.mem_inf.1 (Subgroup.mem_subgroupOf.1 hδ)).1
      (Subgroup.mem_inf.1 (Subgroup.mem_subgroupOf.1 hδ)).2 _) C (fun x => hC x.1 x.2)
  have hres : μ'.restrict (semiMap N s '' (Set.univ ×ˢ 𝓝)) = (μ.prod (ν.restrict 𝓝)).map (semiMap N s) := by
    rw [← he, hme.restrict_map, Set.preimage_image_eq _ hi, ← Measure.prod_restrict, Measure.restrict_univ]
  rw [IntegrableOn, hres, hme.integrable_map_iff] at hI
  refine ⟨hI.integral_prod_left, hE.trans ?_⟩
  rw [hres, hme.integral_map]
  exact integral_prod (Function.uncurry fun h (n : N) => φ (n.1 * s h)) hI

end GlobalTheory.SemiUnfold

end
