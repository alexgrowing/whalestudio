import Mathlib
import Development.AutomorphicArithmetic.LocalEmbeddings.ConeBDefs
open MeasureTheory FreeSingleHomotopyEquivDiscreteChains.UpperTheory.Dv.ConeB

private theorem iter_ne_zero : ∀ {α β : Type} [TopologicalSpace α] [MeasurableSpace α] [BorelSpace α] [SecondCountableTopology α]
    [TopologicalSpace β] [MeasurableSpace β] [BorelSpace β] [SecondCountableTopology β]
    (μa : Measure α) (μb : Measure β) [IsFiniteMeasureOnCompacts μa] [IsFiniteMeasureOnCompacts μb]
    [μa.IsOpenPosMeasure] [μb.IsOpenPosMeasure] [SFinite μa] [SFinite μb]
    (F : α → β → ℂ) (hF : Continuous (Function.uncurry F)) (C : Set (α × β)) (hC : IsCompact C)
    (h0 : ∀ p ∉ C, F p.1 p.2 = 0) (c : ℂ) (hpos : ∀ a b, 0 ≤ (starRingEnd ℂ c * F a b).re) (a₀ : α) (b₀ : β)
    (h₀ : 0 < (starRingEnd ℂ c * F a₀ b₀).re),
    ∫ a, ∫ b, F a b ∂μb ∂μa ≠ 0 := by
  intro α β _ _ _ _ _ _ _ _ μa μb _ _ _ _ _ _ F hF C hC h0 c hpos a₀ b₀ h₀
  set G : α × β → ℂ := Function.uncurry F with hG
  have hsub : Function.support G ⊆ C := by
    intro p hp
    by_contra hpC
    exact hp (h0 p hpC)
  obtain ⟨M, hM⟩ := hC.exists_bound_of_continuousOn hF.continuousOn
  have hbound : ∀ p, ‖G p‖ ≤ max M 0 := by
    intro p
    by_cases hp : p ∈ C
    · exact (hM p hp).trans (le_max_left _ _)
    · have : G p = 0 := h0 p hp
      rw [this, norm_zero]; exact le_max_right _ _
  have hintC : IntegrableOn G C (μa.prod μb) :=
    Measure.integrableOn_of_bounded (M := max M 0) hC.measure_lt_top.ne
      hF.aestronglyMeasurable (Filter.Eventually.of_forall hbound)
  have hint : Integrable G (μa.prod μb) := (integrableOn_iff_integrable_of_support_subset hsub).1 hintC
  have hprod : ∫ p, G p ∂(μa.prod μb) = ∫ a, ∫ b, F a b ∂μb ∂μa := integral_prod G hint
  intro hzero
  have hint2 : Integrable (fun p => starRingEnd ℂ c * G p) (μa.prod μb) := hint.const_mul _
  have hre : ∫ p, (starRingEnd ℂ c * G p).re ∂(μa.prod μb) = 0 := by
    have := integral_re hint2
    rw [integral_const_mul, hprod, hzero, mul_zero] at this
    simpa using this
  have hcont : Continuous (fun p : α × β => (starRingEnd ℂ c * G p).re) :=
    Complex.continuous_re.comp (continuous_const.mul hF)
  have hnn : 0 ≤ fun p : α × β => (starRingEnd ℂ c * G p).re := fun p => hpos p.1 p.2
  have hpos2 : 0 < ∫ p, (starRingEnd ℂ c * G p).re ∂(μa.prod μb) := by
    rw [integral_pos_iff_support_of_nonneg hnn (Complex.reCLM.integrable_comp hint2)]
    have hopen : IsOpen (Function.support fun p : α × β => (starRingEnd ℂ c * G p).re) :=
      hcont.isOpen_support
    refine hopen.measure_pos _ ⟨(a₀, b₀), ?_⟩
    exact ne_of_gt h₀
  linarith

private theorem contOn_dwt {ι : Type} [Fintype ι] (κ : ι → ℤ) (e : ℕ) :
    ContinuousOn (dwt κ e) {y : ι → ℂ | ∀ w, y w ≠ 0} := by
  unfold dwt
  refine ContinuousOn.inv₀ (ContinuousOn.mul ?_ (Complex.continuous_ofReal.comp continuous_nm).continuousOn) ?_
  · unfold wt
    refine continuousOn_finset_prod _ fun w _ => ?_
    have h : Continuous fun s : ι → ℂ => (‖s w‖ : ℂ) := Complex.continuous_ofReal.comp (continuous_apply w).norm
    have h0 : ∀ s ∈ {y : ι → ℂ | ∀ w, y w ≠ 0}, (‖s w‖ : ℂ) ≠ 0 := fun s hs => by
      exact_mod_cast norm_ne_zero_iff.2 (hs w)
    refine ContinuousOn.mul (ContinuousOn.zpow₀ ((continuous_apply w).continuousOn.div h.continuousOn h0) _ ?_)
      (h.pow _).continuousOn
    exact fun s hs => Or.inl (div_ne_zero (hs w) (h0 s hs))
  · intro y hy
    exact mul_ne_zero (wt_ne_zero κ e hy) (by exact_mod_cast (nm_pos hy).ne')

private theorem compact_pre {ι : Type} [Fintype ι] {n : ℕ} {K : Type} [TopologicalSpace K] [CompactSpace K]
    (η : K → Fin n × ι → ℂ) (hη : Continuous η) (h0 : ∀ k w, ∃ i, η k (i, w) ≠ 0)
    (hπ : Continuous fun p : K × (ι → ℂ) => sc p.2 (η p.1)) (x : Fin n × ι → ℂ) (r : ℝ) :
    IsCompact ((fun p : K × (ι → ℂ) => sc p.2 (η p.1)) ⁻¹' Metric.closedBall x r) := by
  have hm : ∀ w : ι, ∃ m : ℝ, 0 < m ∧ ∀ k ∈ (Set.univ : Set K), m ≤ ‖fun i : Fin n => η k (i, w)‖ := by
    intro w
    refine isCompact_univ.exists_forall_le' (Continuous.continuousOn (by fun_prop)) fun k _ => ?_
    obtain ⟨i, hi⟩ := h0 k w
    exact norm_pos_iff.2 fun h => hi (congrFun h i)
  choose m hm0 hm using hm
  have hc : IsCompact ((Set.univ : Set K) ×ˢ (Set.pi Set.univ fun w : ι => Metric.closedBall (0 : ℂ) ((‖x‖ + r) / m w))) :=
    isCompact_univ.prod (isCompact_univ_pi fun w => isCompact_closedBall _ _)
  refine hc.of_isClosed_subset (Metric.isClosed_closedBall.preimage hπ) ?_
  rintro ⟨k, y⟩ hp
  refine ⟨trivial, fun w _ => ?_⟩
  have h1 : ‖sc y (η k)‖ ≤ ‖x‖ + r := norm_le_of_mem_closedBall hp
  have h2 : ‖y w • fun i : Fin n => η k (i, w)‖ ≤ ‖sc y (η k)‖ :=
    (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun i => norm_le_pi_norm (sc y (η k)) (i, w)
  rw [norm_smul] at h2
  rw [mem_closedBall_zero_iff, le_div_iff₀ (hm0 w)]
  have h3 := mul_le_mul_of_nonneg_left (hm w k trivial) (norm_nonneg (y w))
  exact h3.trans (h2.trans h1)

theorem UpperTheory.fourier_continuous_nonvanishing :
    ∀ {ι : Type} [Fintype ι] {n : ℕ} {K : Type} [TopologicalSpace K] [CompactSpace K] [SecondCountableTopology K]
        [MeasurableSpace K] [BorelSpace K] (μ : Measure K) [IsFiniteMeasure μ] [μ.IsOpenPosMeasure]
        (η : K → Fin n × ι → ℂ), Continuous η → (∀ k w, ∃ i, η k (i, w) ≠ 0) →
        ∀ (G : K → (ι → ℂ) → ℂ), Continuous (Function.uncurry G) → ∀ (κ : ι → ℤ) (e : ℕ) (k₀ : K) (y₀ : ι → ℂ), (∀ w, y₀ w ≠ 0) →
        ∀ c : ℂ, (∀ k y, sc y (η k) = sc y₀ (η k₀) → 0 < (starRingEnd ℂ c * (G k y * dwt κ e y)).re) →
        ∃ β : (Fin n × ι → ℂ) → ℂ, ContDiff ℝ (⊤ : ℕ∞) β ∧ HasCompactSupport β ∧
          (∀ k, Integrable fun y => β (sc y (η k)) * G k y * dwt κ e y) ∧
          ∫ k, ∫ y, β (sc y (η k)) * G k y * dwt κ e y ∂volume ∂μ ≠ 0 := by
  intro ι _ n K _ _ _ _ _ μ _ _ η hη h0 G hG κ e k₀ y₀ hy₀ c hc
  have hπ : Continuous fun p : K × (ι → ℂ) => sc p.2 (η p.1) := by
    unfold sc
    fun_prop
  set π : K × (ι → ℂ) → (Fin n × ι → ℂ) := fun p => sc p.2 (η p.1) with hπdef
  set x₀ := sc y₀ (η k₀) with hx₀
  set N : Set (K × (ι → ℂ)) := {p | ∀ w, p.2 w ≠ 0} with hN
  have hNo : IsOpen N := by
    have : N = ⋂ w, {p : K × (ι → ℂ) | p.2 w ≠ 0} := by ext p; simp [hN]
    rw [this]
    exact isOpen_iInter_of_finite fun w => isOpen_ne_fun (by fun_prop) continuous_const
  have hH : ContinuousOn (fun p : K × (ι → ℂ) => G p.1 p.2 * dwt κ e p.2) N :=
    hG.continuousOn.mul ((contOn_dwt κ e).comp continuous_snd.continuousOn fun p hp => hp)
  set O : Set (K × (ι → ℂ)) :=
    N ∩ (fun p : K × (ι → ℂ) => (starRingEnd ℂ c * (G p.1 p.2 * dwt κ e p.2)).re) ⁻¹' Set.Ioi 0 with hO
  have hOo : IsOpen O :=
    ContinuousOn.isOpen_inter_preimage
      (Complex.continuous_re.comp_continuousOn (continuousOn_const.mul hH)) hNo isOpen_Ioi
  have hfib : ∀ p, π p = x₀ → p ∈ O := by
    intro p hp
    refine ⟨fun w hw => ?_, hc p.1 p.2 hp⟩
    obtain ⟨i, hi⟩ := h0 k₀ w
    have h1 : p.2 w * η p.1 (i, w) = y₀ w * η k₀ (i, w) := congrFun hp (i, w)
    rw [hw, zero_mul] at h1
    exact mul_ne_zero (hy₀ w) hi h1.symm
  have hT : IsCompact (π '' (π ⁻¹' Metric.closedBall x₀ 1 \ O)) :=
    ((compact_pre η hη h0 hπ x₀ 1).diff hOo).image hπ
  have hx : x₀ ∈ (π '' (π ⁻¹' Metric.closedBall x₀ 1 \ O))ᶜ := by
    rintro ⟨p, hp, hpx⟩
    exact hp.2 (hfib p hpx)
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hT.isClosed.isOpen_compl x₀ hx
  set r : ℝ := min (ε / 2) 1 with hr
  have hr0 : 0 < r := lt_min (by linarith) one_pos
  set C := π ⁻¹' Metric.closedBall x₀ r with hC
  have hCc : IsCompact C := compact_pre η hη h0 hπ x₀ r
  have hCcl : IsClosed C := Metric.isClosed_closedBall.preimage hπ
  have hCO : C ⊆ O := by
    intro p hp
    by_contra hpO
    have h1 : dist (π p) x₀ ≤ r := hp
    refine hball (a := π p) ?_ ⟨p, ⟨?_, hpO⟩, rfl⟩
    · exact lt_of_le_of_lt (h1.trans (min_le_left _ _)) (by linarith)
    · exact h1.trans (min_le_right _ _)
  let b : ContDiffBump x₀ := ⟨r / 2, r, by linarith, by linarith⟩
  have hb0 : ∀ p ∉ C, b (π p) = 0 := fun p hp =>
    b.zero_of_le_dist (le_of_lt (not_le.1 hp))
  have hbc : Continuous fun x => (b x : ℂ) := Complex.continuous_ofReal.comp b.continuous
  have hz : ∀ p ∉ C, (b (π p) : ℂ) * G p.1 p.2 * dwt κ e p.2 = 0 := fun p hp => by
    rw [hb0 p hp]; simp
  have hF : Continuous fun p : K × (ι → ℂ) => (b (π p) : ℂ) * G p.1 p.2 * dwt κ e p.2 := by
    refine continuous_iff_continuousAt.2 fun p => ?_
    by_cases hp : p ∈ C
    · simp only [mul_assoc]
      exact (hbc.comp hπ).continuousAt.mul (hH.continuousAt (hNo.mem_nhds (hCO hp).1))
    · refine (continuousAt_const (y := (0 : ℂ))).congr ?_
      filter_upwards [hCcl.isOpen_compl.mem_nhds hp] with q hq
      exact (hz q hq).symm
  have hFk : ∀ k, Continuous fun y => (b (sc y (η k)) : ℂ) * G k y * dwt κ e y := fun k => by
    have h := hF.comp (Continuous.prodMk_right k)
    simpa only [Function.comp_def, hπdef] using h
  have hre : ∀ p : K × (ι → ℂ), (starRingEnd ℂ c * ((b (π p) : ℂ) * G p.1 p.2 * dwt κ e p.2)).re
      = b (π p) * (starRingEnd ℂ c * (G p.1 p.2 * dwt κ e p.2)).re := fun p => by
    rw [← Complex.re_ofReal_mul]; congr 1; ring
  refine ⟨fun x => (b x : ℂ), Complex.ofRealCLM.contDiff.comp b.contDiff,
    b.hasCompactSupport.comp_left (g := fun t : ℝ => (t : ℂ)) Complex.ofReal_zero, fun k => ?_, ?_⟩
  · refine Continuous.integrable_of_hasCompactSupport (hFk k) ?_
    refine HasCompactSupport.intro (hCc.image continuous_snd) fun y hy => ?_
    exact hz (k, y) fun h => hy ⟨(k, y), h, rfl⟩
  · refine iter_ne_zero μ volume (fun k y => (b (sc y (η k)) : ℂ) * G k y * dwt κ e y) hF C hCc hz c (fun k y => ?_) k₀ y₀ ?_
    · by_cases hp : (k, y) ∈ C
      · rw [show (starRingEnd ℂ c * ((b (sc y (η k)) : ℂ) * G k y * dwt κ e y)).re = _ from hre (k, y)]
        exact mul_nonneg b.nonneg (le_of_lt (hCO hp).2)
      · rw [show (b (sc y (η k)) : ℂ) * G k y * dwt κ e y = 0 from hz (k, y) hp]; simp
    · rw [show (starRingEnd ℂ c * ((b (sc y₀ (η k₀)) : ℂ) * G k₀ y₀ * dwt κ e y₀)).re = _ from hre (k₀, y₀)]
      refine mul_pos (b.pos_of_mem_ball ?_) (hc k₀ y₀ rfl)
      exact Metric.mem_ball_self hr0
