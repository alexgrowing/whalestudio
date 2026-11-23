import Mathlib
open scoped NNReal ENNReal
open MeasureTheory
open scoped Pointwise

namespace GlobalTheory.FoldLe

theorem tsum_lintegral_le {α ι : Type} [MeasurableSpace α] (μ : Measure α) (f : ι → α → ℝ≥0∞) :
    ∑' i, ∫⁻ x, f i x ∂μ ≤ ∫⁻ x, ∑' i, f i x ∂μ := by
  classical
  rw [ENNReal.tsum_eq_iSup_sum]
  refine iSup_le fun s => ?_
  calc ∑ i ∈ s, ∫⁻ x, f i x ∂μ ≤ ∫⁻ x, ∑ i ∈ s, f i x ∂μ := by
        induction s using Finset.induction_on with
        | empty => simp
        | insert a s ha ih =>
          simp_rw [Finset.sum_insert ha]
          exact (add_le_add le_rfl ih).trans (le_lintegral_add (f a) (fun x => ∑ i ∈ s, f i x))
    _ ≤ ∫⁻ x, ∑' i, f i x ∂μ := lintegral_mono fun x => ENNReal.sum_le_tsum _

theorem ae_of_iter_lintegral_eq_zero {N G₁ L Kt : Type} [MeasurableSpace N] [MeasurableSpace G₁]
    [MeasurableSpace L] [MeasurableSpace Kt]
    (μN : Measure N) (ν : Measure G₁) (μL : Measure L) (μK : Measure Kt)
    [SFinite μN] [SFinite ν] [SFinite μL]
    (F : N × G₁ × L × Kt → ℝ≥0∞) (hF : Measurable F)
    (h0 : ∫⁻ k, ∫⁻ l, ∫⁻ g₀, ∫⁻ n, F (n, g₀, l, k) ∂μN ∂ν ∂μL ∂μK = 0) :
    ∀ᵐ k ∂μK, ∀ᵐ l ∂μL, ∀ᵐ g₀ ∂ν, ∀ᵐ n ∂μN, F (n, g₀, l, k) = 0 := by
  have h1 : Measurable fun y : G₁ × L × Kt => ∫⁻ n, F (n, y) ∂μN := hF.lintegral_prod_left'
  have h2 : Measurable fun y : L × Kt => ∫⁻ g₀, ∫⁻ n, F (n, g₀, y) ∂μN ∂ν :=
    h1.lintegral_prod_left'
  have h3 : Measurable fun k : Kt => ∫⁻ l, ∫⁻ g₀, ∫⁻ n, F (n, g₀, l, k) ∂μN ∂ν ∂μL :=
    h2.lintegral_prod_left'
  have e3 := (lintegral_eq_zero_iff h3).1 h0
  filter_upwards [e3] with k hk
  have hk' : ∫⁻ l, ∫⁻ g₀, ∫⁻ n, F (n, g₀, l, k) ∂μN ∂ν ∂μL = 0 := hk
  have e2 := (lintegral_eq_zero_iff (h2.comp measurable_prodMk_right)).1 hk'
  filter_upwards [e2] with l hl
  have hl' : ∫⁻ g₀, ∫⁻ n, F (n, g₀, l, k) ∂μN ∂ν = 0 := hl
  have e1 := (lintegral_eq_zero_iff (h1.comp measurable_prodMk_right)).1 hl'
  filter_upwards [e1] with g₀ hg
  have hg' : ∫⁻ n, F (n, g₀, l, k) ∂μN = 0 := hg
  have e0 := (lintegral_eq_zero_iff (hF.comp measurable_prodMk_right)).1 hg'
  filter_upwards [e0] with n hn
  exact hn

theorem measurableConstSMul_subgroup {X : Type} [Group X] [MeasurableSpace X] (H : Subgroup X)
    (hmul : ∀ g : X, Measurable (g * ·)) : MeasurableConstSMul H X :=
  ⟨fun γ => hmul (γ : X)⟩

theorem smulInvariant_subgroup {X : Type} [Group X] [MeasurableSpace X] (H : Subgroup X)
    (μ : Measure X) [μ.IsMulLeftInvariant] (hmul : ∀ g : X, Measurable (g * ·)) :
    SMulInvariantMeasure H X μ :=
  ⟨fun γ s hs => by
    show μ (((γ : X) * ·) ⁻¹' s) = μ s
    rw [← Measure.map_apply (hmul _) hs, map_mul_left_eq_self]⟩

theorem unfold_le {G₁ : Type} [Group G₁] [MeasurableSpace G₁] (ν : Measure G₁) (Γ : Subgroup G₁)
    [Countable Γ] (hmul : ∀ g : G₁, Measurable (g * ·)) [ν.IsMulLeftInvariant] (dom : Set G₁)
    (hdom : IsFundamentalDomain Γ dom ν) (P H : G₁ → ℝ≥0∞) (hH : ∀ γ ∈ Γ, ∀ g, H (γ * g) = H g)
    (C : ℝ≥0∞) (hC : C ≠ ⊤) (hP : ∀ᵐ g ∂ν.restrict dom, ∑' γ : Γ, P ((γ : G₁) * g) ≤ C) :
    ∫⁻ g, P g * H g ∂ν ≤ C * ∫⁻ g in dom, H g ∂ν := by
  haveI := measurableConstSMul_subgroup Γ hmul
  haveI := smulInvariant_subgroup Γ ν hmul
  calc ∫⁻ g, P g * H g ∂ν = ∑' γ : Γ, ∫⁻ g in dom, P (γ • g) * H (γ • g) ∂ν :=
        hdom.lintegral_eq_tsum'' _
    _ = ∑' γ : Γ, ∫⁻ g in dom, P ((γ : G₁) * g) * H g ∂ν := by
        congr 1; ext γ; congr 1; ext g
        rw [Subgroup.smul_def, smul_eq_mul, hH γ γ.2]
    _ ≤ ∫⁻ g in dom, ∑' γ : Γ, P ((γ : G₁) * g) * H g ∂ν := tsum_lintegral_le _ _
    _ = ∫⁻ g in dom, (∑' γ : Γ, P ((γ : G₁) * g)) * H g ∂ν := by
        simp_rw [ENNReal.tsum_mul_right]
    _ ≤ ∫⁻ g in dom, C * H g ∂ν := lintegral_mono_ae (hP.mono fun g hg => by gcongr)
    _ = C * ∫⁻ g in dom, H g ∂ν := lintegral_const_mul' _ _ hC

end GlobalTheory.FoldLe

namespace GlobalTheory.FoldLe

theorem sum_translates_le {G G₁ : Type} [Group G] [MeasurableSpace G] [Group G₁]
    (N Q : Subgroup G) (Γ : Subgroup G₁) (μN : Measure N) (ι : G₁ → G) (𝓕 : Set N) (D₀ : Set G)
    [Countable Q] [Countable Γ] (hD₀ : MeasurableSet D₀)
    (hmulG : ∀ g : G, Measurable (g * ·)) (hmulrG : ∀ g : G, Measurable (· * g))
    (hιQ : ∀ γ ∈ Γ, ι γ ∈ Q) (huniq : ∀ q ∈ Q, ∃! γ : Γ, (ι γ)⁻¹ * q ∈ N)
    (hswap : ∀ γ ∈ Γ, ∀ f : G → ℝ≥0∞, Measurable f → ∫⁻ n, f (n.1 * ι γ) ∂μN = ∫⁻ n, f (ι γ * n.1) ∂μN)
    [μN.IsMulLeftInvariant] (h𝓕 : IsFundamentalDomain (Q.subgroupOf N) 𝓕 μN)
    (x : G) (hx : ∀ᵐ n ∂μN, ∑' q : Q, D₀.indicator 1 ((q : G) * (n.1 * x)) ≤ (1 : ℝ≥0∞)) :
    ∑' γ : Γ, ∫⁻ n, D₀.indicator 1 (n.1 * ι γ * x) ∂μN ≤ μN 𝓕 := by
  haveI : Countable (Q.subgroupOf N) := by
    refine Function.Injective.countable
      (f := fun ν : Q.subgroupOf N => (⟨((ν : N) : G), Subgroup.mem_subgroupOf.1 ν.2⟩ : Q)) ?_
    intro a b h
    have h' : ((a : N) : G) = ((b : N) : G) := by simpa using congrArg Subtype.val h
    exact Subtype.ext (Subtype.ext h')
  have hmulN : ∀ g : N, Measurable (g * ·) := fun g =>
    ((hmulG (g : G)).comp measurable_subtype_coe).subtype_mk
  haveI := measurableConstSMul_subgroup (Q.subgroupOf N) hmulN
  haveI := smulInvariant_subgroup (Q.subgroupOf N) μN hmulN
  have hmeas : Measurable fun y : G => D₀.indicator (1 : G → ℝ≥0∞) (y * x) :=
    (measurable_const.indicator hD₀).comp (hmulrG x)

  have hmemQ : ∀ p : Γ × Q.subgroupOf N, ι p.1 * ((p.2 : N) : G) ∈ Q := fun p =>
    Q.mul_mem (hιQ _ p.1.2) (Subgroup.mem_subgroupOf.1 p.2.2)
  let e : Γ × Q.subgroupOf N → Q := fun p => ⟨ι p.1 * ((p.2 : N) : G), hmemQ p⟩
  have he : Function.Injective e := by
    rintro ⟨γ, ν⟩ ⟨γ', ν'⟩ h
    have h' : ι γ * ((ν : N) : G) = ι γ' * ((ν' : N) : G) := congrArg Subtype.val h
    obtain ⟨γ₀, -, hγ₀⟩ := huniq _ (hmemQ (γ, ν))
    have h1 : γ = γ₀ := hγ₀ γ (by simp)
    have h2 : γ' = γ₀ := hγ₀ γ' (by
      show (ι γ')⁻¹ * (ι γ * ((ν : N) : G)) ∈ N
      rw [h']; simp)
    have hγ : γ = γ' := h1.trans h2.symm
    subst hγ
    have : ((ν : N) : G) = ((ν' : N) : G) := mul_left_cancel h'
    have : ν = ν' := Subtype.ext (Subtype.ext this)
    rw [this]
  calc ∑' γ : Γ, ∫⁻ n, D₀.indicator 1 (n.1 * ι γ * x) ∂μN
      = ∑' γ : Γ, ∑' ν : Q.subgroupOf N, ∫⁻ n in 𝓕,
          D₀.indicator 1 (ι γ * ((ν : N) : G) * (n.1 * x)) ∂μN := by
        congr 1; ext γ
        rw [hswap γ γ.2 _ hmeas, h𝓕.lintegral_eq_tsum'']
        congr 1; ext ν; congr 1; ext n
        simp only [Subgroup.smul_def, smul_eq_mul, Subgroup.coe_mul, mul_assoc]
    _ ≤ ∑' γ : Γ, ∫⁻ n in 𝓕, ∑' ν : Q.subgroupOf N,
          D₀.indicator 1 (ι γ * ((ν : N) : G) * (n.1 * x)) ∂μN :=
        ENNReal.tsum_le_tsum fun γ => tsum_lintegral_le _ _
    _ ≤ ∫⁻ n in 𝓕, ∑' γ : Γ, ∑' ν : Q.subgroupOf N,
          D₀.indicator 1 (ι γ * ((ν : N) : G) * (n.1 * x)) ∂μN := tsum_lintegral_le _ _
    _ ≤ ∫⁻ n in 𝓕, ∑' q : Q, D₀.indicator 1 ((q : G) * (n.1 * x)) ∂μN := by
        refine lintegral_mono fun n => ?_
        rw [← ENNReal.tsum_prod]
        exact ENNReal.tsum_comp_le_tsum_of_injective he
          (fun q : Q => D₀.indicator (1 : G → ℝ≥0∞) ((q : G) * (n.1 * x)))
    _ ≤ ∫⁻ n in 𝓕, 1 ∂μN := lintegral_mono_ae (ae_restrict_of_ae hx)
    _ = μN 𝓕 := setLIntegral_one _

end GlobalTheory.FoldLe

namespace GlobalTheory

open GlobalTheory.FoldLe in

theorem foldBound_le : ∀ {G G₁ L Kt : Type} [Group G] [MeasurableSpace G] [Group G₁] [MeasurableSpace G₁] [MeasurableSpace L] [MeasurableSpace Kt] (μG : Measure G) (ν : Measure G₁) (μL : Measure L) (μK : Measure Kt) (N Q : Subgroup G) (Γ : Subgroup G₁) (μN : Measure N) (kk : Kt → G) (m : L → G₁ → G) (ι : G₁ → G) (w : L → ℝ≥0∞) (c : ℝ≥0∞) (dom : Set G₁) (𝓕 : Set N), Countable Q → Countable Γ → SFinite ν → SFinite μL → SFinite μN → (∀ g : G, Measurable (g * ·)) → (∀ g : G₁, Measurable (g * ·)) → (∀ g : G, Measurable (· * g)) → Measurable (fun p : N × G₁ × L × Kt => p.1.1 * m p.2.2.1 p.2.1 * kk p.2.2.2) → Measurable w → (∀ l, w l ≠ 0) → (∀ l, w l ≠ ⊤) → μG.IsMulLeftInvariant → (∀ φ : G → ℝ≥0∞, Measurable φ → ∫⁻ g, φ g ∂μG = c * ∫⁻ k, ∫⁻ l, ∫⁻ g₀, ∫⁻ n, φ (n.1 * m l g₀ * kk k) * w l ∂μN ∂ν ∂μL ∂μK) → c ≠ 0 → c ≠ ⊤ → (∀ l g₀, ∀ γ ∈ Γ, m l (γ * g₀) = ι γ * m l g₀) → (∀ γ ∈ Γ, ι γ ∈ Q) → (∀ q ∈ Q, ∃! γ : Γ, (ι γ)⁻¹ * q ∈ N) → (∀ γ ∈ Γ, ∀ f : G → ℝ≥0∞, Measurable f → ∫⁻ n, f (n.1 * ι γ) ∂μN = ∫⁻ n, f (ι γ * n.1) ∂μN) → μN.IsMulLeftInvariant → IsFundamentalDomain (Q.subgroupOf N) 𝓕 μN → μN 𝓕 ≠ ⊤ → IsFundamentalDomain Γ dom ν → ν.IsMulLeftInvariant → ∀ 𝓓 : Set G, IsFundamentalDomain Q 𝓓 μG → ∀ f : G → ℝ≥0∞, AEMeasurable f μG → (∀ q ∈ Q, ∀ g, f (q * g) = f g) → (∀ n ∈ N, ∀ g, f (n * g) = f g) → ∫⁻ g in 𝓓, f g ∂μG ≤ c * μN 𝓕 * ∫⁻ k, ∫⁻ l, ∫⁻ g₀ in dom, f (m l g₀ * kk k) * w l ∂ν ∂μL ∂μK := by
  intro G G₁ L Kt _ _ _ _ _ _ μG ν μL μK N Q Γ μN kk m ι w c dom 𝓕 hQc hΓc hνs hLs hNs hmulG hmulG₁
    hmulrG hΦ hw hw0 hwtop hμGinv hform hc0 hctop hmγ hιQ huniq hswap hμNinv h𝓕 h𝓕top hdom hνinv
    𝓓 h𝓓 f hf hfQ hfN
  haveI := hνs; haveI := hLs; haveI := hNs; haveI := hQc; haveI := hΓc
  haveI := hμGinv; haveI := hμNinv; haveI := hνinv
  haveI := measurableConstSMul_subgroup Q hmulG
  haveI := smulInvariant_subgroup Q μG hmulG
  obtain ⟨D₀, hD₀sub, hD₀m, hD₀ae⟩ := h𝓓.nullMeasurableSet.exists_measurable_subset_ae_eq
  set f' := hf.mk f with hf'def
  have hf'm : Measurable f' := hf.measurable_mk
  have hff' : f =ᵐ[μG] f' := hf.ae_eq_mk
  set Z₀ := toMeasurable μG {g | f g ≠ f' g} with hZ₀def
  have hZ₀m : MeasurableSet Z₀ := measurableSet_toMeasurable _ _
  have hZ₀0 : μG Z₀ = 0 := by rw [hZ₀def, measure_toMeasurable]; exact ae_iff.1 hff'
  let E : Set G := ⋃ q : Q, ⋃ q' : Q, ⋃ (_ : q ≠ q'),
    ((q : G) * ·) ⁻¹' D₀ ∩ ((q' : G) * ·) ⁻¹' D₀
  have hEm : MeasurableSet E :=
    MeasurableSet.iUnion fun q => MeasurableSet.iUnion fun q' => MeasurableSet.iUnion fun _ =>
      (hD₀m.preimage (hmulG _)).inter (hD₀m.preimage (hmulG _))
  have hE0 : μG E = 0 := by
    refine measure_iUnion_null fun q => measure_iUnion_null fun q' =>
      measure_iUnion_null fun hqq => ?_
    have hne : q⁻¹ ≠ q'⁻¹ := fun h => hqq (inv_injective h)
    have hdis : μG (q⁻¹ • 𝓓 ∩ q'⁻¹ • 𝓓) = 0 := h𝓓.aedisjoint hne
    refine measure_mono_null ?_ hdis
    rintro y ⟨h1, h2⟩
    refine ⟨?_, ?_⟩
    · rw [Set.mem_smul_set_iff_inv_smul_mem, inv_inv]; exact hD₀sub h1
    · rw [Set.mem_smul_set_iff_inv_smul_mem, inv_inv]; exact hD₀sub h2
  have hsum1 : ∀ y ∉ E, ∑' q : Q, D₀.indicator (1 : G → ℝ≥0∞) ((q : G) * y) ≤ 1 := by
    intro y hy
    by_cases h : ∃ q : Q, (q : G) * y ∈ D₀
    · obtain ⟨q₀, hq₀⟩ := h
      rw [tsum_eq_single q₀]
      · simp [Set.indicator_of_mem hq₀]
      · intro q hq
        refine Set.indicator_apply_eq_zero.2 fun hqD => ?_
        exfalso
        exact hy (Set.mem_iUnion.2 ⟨q, Set.mem_iUnion.2 ⟨q₀, Set.mem_iUnion.2 ⟨hq, hqD, hq₀⟩⟩⟩)
    · push_neg at h
      simp [Set.indicator_apply, h]
  have hpull : ∀ Z : Set G, MeasurableSet Z → μG Z = 0 →
      ∀ᵐ k ∂μK, ∀ᵐ l ∂μL, ∀ᵐ g₀ ∂ν, ∀ᵐ n ∂μN, n.1 * m l g₀ * kk k ∉ Z := by
    intro Z hZ hZ0
    have hF : Measurable fun p : N × G₁ × L × Kt =>
        Z.indicator (1 : G → ℝ≥0∞) (p.1.1 * m p.2.2.1 p.2.1 * kk p.2.2.2) * w p.2.2.1 :=
      ((measurable_one.indicator hZ).comp hΦ).mul
        (hw.comp (measurable_fst.comp (measurable_snd.comp measurable_snd)))
    have h0 := hform (Z.indicator (1 : G → ℝ≥0∞)) (measurable_one.indicator hZ)
    rw [lintegral_indicator_one hZ, hZ0] at h0
    have h0' := (mul_eq_zero.1 h0.symm).resolve_left hc0
    have h4 := ae_of_iter_lintegral_eq_zero μN ν μL μK _ hF h0'
    filter_upwards [h4] with k hk
    filter_upwards [hk] with l hl
    filter_upwards [hl] with g₀ hg
    filter_upwards [hg] with n hn
    intro hmem
    simp only [Set.indicator_of_mem hmem, Pi.one_apply, one_mul] at hn
    exact hw0 l hn
  have hgood := hpull (Z₀ ∪ E) (hZ₀m.union hEm) (measure_union_null hZ₀0 hE0)
  have hInd : ∀ l g₀ k, Measurable fun n : N => D₀.indicator (1 : G → ℝ≥0∞) (n.1 * m l g₀ * kk k) :=
    fun l g₀ k => (measurable_const.indicator hD₀m).comp
      (hΦ.comp (measurable_prodMk_right (y := ((g₀, l, k) : G₁ × L × Kt))))
  calc ∫⁻ g in 𝓓, f g ∂μG = ∫⁻ g in D₀, f g ∂μG := (setLIntegral_congr hD₀ae).symm
    _ = ∫⁻ g, D₀.indicator f' g ∂μG := by
        rw [lintegral_indicator hD₀m]
        exact lintegral_congr_ae (ae_restrict_of_ae hff')
    _ = c * ∫⁻ k, ∫⁻ l, ∫⁻ g₀, ∫⁻ n, D₀.indicator f' (n.1 * m l g₀ * kk k) * w l ∂μN ∂ν ∂μL ∂μK :=
        hform _ (hf'm.indicator hD₀m)
    _ = c * ∫⁻ k, ∫⁻ l, ∫⁻ g₀, (∫⁻ n, D₀.indicator (1 : G → ℝ≥0∞) (n.1 * m l g₀ * kk k) ∂μN) *
          (f (m l g₀ * kk k) * w l) ∂ν ∂μL ∂μK := by
        congr 1
        refine lintegral_congr_ae (hgood.mono fun k hk => ?_)
        refine lintegral_congr_ae (hk.mono fun l hl => ?_)
        refine lintegral_congr_ae (hl.mono fun g₀ hg => ?_)
        dsimp only
        rw [← lintegral_mul_const _ (hInd l g₀ k)]
        refine lintegral_congr_ae (hg.mono fun n hn => ?_)
        have hnZ : n.1 * m l g₀ * kk k ∉ Z₀ := fun h => hn (Or.inl h)
        have h1 : f' (n.1 * m l g₀ * kk k) = f (n.1 * m l g₀ * kk k) := by
          by_contra hne
          exact hnZ (subset_toMeasurable _ _ (fun h => hne h.symm))
        have h2 : f (n.1 * m l g₀ * kk k) = f (m l g₀ * kk k) := by
          rw [mul_assoc]; exact hfN _ n.2 _
        by_cases hD : n.1 * m l g₀ * kk k ∈ D₀
        · simp [Set.indicator_of_mem hD, h1, h2]
        · simp [Set.indicator_apply, hD]
    _ ≤ c * ∫⁻ k, ∫⁻ l, μN 𝓕 * ∫⁻ g₀ in dom, f (m l g₀ * kk k) * w l ∂ν ∂μL ∂μK := by
        gcongr c * ?_
        refine lintegral_mono_ae (hgood.mono fun k hk => ?_)
        refine lintegral_mono_ae (hk.mono fun l hl => ?_)
        refine unfold_le ν Γ hmulG₁ dom hdom
          (fun g₀ => ∫⁻ n, D₀.indicator (1 : G → ℝ≥0∞) (n.1 * m l g₀ * kk k) ∂μN)
          (fun g₀ => f (m l g₀ * kk k) * w l) ?_ (μN 𝓕) h𝓕top ?_
        · intro γ hγ g₀
          simp only [hmγ l g₀ γ hγ, mul_assoc]
          rw [hfQ _ (hιQ γ hγ)]
        · refine ae_restrict_of_ae (hl.mono fun g₀ hg => ?_)
          have hx : ∀ᵐ n ∂μN, ∑' q : Q,
              D₀.indicator (1 : G → ℝ≥0∞) ((q : G) * (n.1 * (m l g₀ * kk k))) ≤ 1 :=
            hg.mono fun n hn => hsum1 _ (fun h => hn (Or.inr (by rwa [← mul_assoc] at h)))
          have h5 := sum_translates_le N Q Γ μN ι 𝓕 D₀ hD₀m hmulG hmulrG hιQ huniq hswap h𝓕 _ hx
          refine (le_of_eq ?_).trans h5
          congr 1; ext γ; congr 1; ext n
          rw [hmγ l g₀ γ γ.2]; simp only [mul_assoc]
    _ = c * μN 𝓕 * ∫⁻ k, ∫⁻ l, ∫⁻ g₀ in dom, f (m l g₀ * kk k) * w l ∂ν ∂μL ∂μK := by
        rw [mul_assoc]; congr 1
        rw [← lintegral_const_mul' _ _ h𝓕top]
        congr 1; ext k
        exact lintegral_const_mul' _ _ h𝓕top

end GlobalTheory
