import ReciprocityTheory.L2DbarEstimates.HormanderEstimate.ClosedSt

namespace ReciprocityTheory.L2DbarEstimates.F

open MeasureTheory Filter Topology Set
open scoped ENNReal

noncomputable section

theorem continuous_of_smoothR (n : ℕ) {M : Type*} [TopologicalSpace M] (z : M → V n)
    (hz : IsLocalHomeomorph z) (ψ : M → ℝ) (hψ : SmoothR n z ψ) : Continuous ψ := by
  rw [continuous_iff_continuousAt]
  intro x
  obtain ⟨e, hxe, he⟩ := hz x
  have hc : IsChart n z e := fun y _ => by rw [he]
  have hf := (hψ e hc).continuousOn.continuousAt (e.open_target.mem_nhds (e.map_source hxe))
  have h2 := hf.comp (e.continuousAt hxe)
  have h3 : ContinuousAt (fun y => (ψ y : ℂ)) x := by
    refine h2.congr (Filter.eventually_of_mem (e.open_source.mem_nhds hxe) (fun y hy => ?_))
    simp [Function.comp, e.left_inv hy]
  have h4 : ContinuousAt (fun y => ((ψ y : ℂ)).re) x := Complex.continuous_re.continuousAt.comp h3
  simpa using h4

theorem exists_lintegral_compact_le (n : ℕ) {M : Type*} [TopologicalSpace M] [T2Space M]
    [MeasurableSpace M] [BorelSpace M] (z : M → V n) (ψ : M → ℝ) (hψ : Continuous ψ)
    (K : Set M) (hK : IsCompact K) :
    ∃ c : ℝ, ∀ g : M → ℂ, ∫⁻ x in K, ‖g x‖ₑ ^ 2 ∂vol n z ≤ ENNReal.ofReal c * wint n z g ψ := by
  obtain ⟨C, hC⟩ := hK.bddAbove_image hψ.continuousOn
  refine ⟨Real.exp C, fun g => ?_⟩
  unfold wint
  calc ∫⁻ x in K, ‖g x‖ₑ ^ 2 ∂vol n z
      ≤ ∫⁻ x in K, ENNReal.ofReal (Real.exp C) *
          ENNReal.ofReal (‖g x‖ ^ 2 * Real.exp (-ψ x)) ∂vol n z := by
        refine setLIntegral_mono' hK.measurableSet (fun x hx => ?_)
        have hψx : ψ x ≤ C := hC ⟨x, hx, rfl⟩
        rw [← ENNReal.ofReal_mul (Real.exp_pos C).le]
        have h1 : ‖g x‖ₑ ^ 2 = ENNReal.ofReal (‖g x‖ ^ 2) := by
          rw [← ofReal_norm_eq_enorm, ← ENNReal.ofReal_pow (norm_nonneg _)]
        rw [h1]
        apply ENNReal.ofReal_le_ofReal
        have hexp : 1 ≤ Real.exp C * Real.exp (-ψ x) := by
          rw [← Real.exp_add]
          exact Real.one_le_exp (by linarith)
        have h2 : Real.exp C * (‖g x‖ ^ 2 * Real.exp (-ψ x)) =
            ‖g x‖ ^ 2 * (Real.exp C * Real.exp (-ψ x)) := by ring
        rw [h2]
        exact le_mul_of_one_le_right (sq_nonneg _) hexp
    _ = ENNReal.ofReal (Real.exp C) *
          ∫⁻ x in K, ENNReal.ofReal (‖g x‖ ^ 2 * Real.exp (-ψ x)) ∂vol n z := by
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    _ ≤ ENNReal.ofReal (Real.exp C) *
          ∫⁻ x, ENNReal.ofReal (‖g x‖ ^ 2 * Real.exp (-ψ x)) ∂vol n z :=
        mul_le_mul_of_nonneg_left (setLIntegral_le_lintegral _ _) (by simp)

private theorem chart_symm_eventuallyEq_of_mem_sources (n : ℕ) {M : Type*} [TopologicalSpace M] (z : M → V n)
    {e e' : OpenPartialHomeomorph M (V n)} (he : IsChart n z e) (he' : IsChart n z e') {x : M}
    (hx : x ∈ e.source) (hx' : x ∈ e'.source) : e.symm =ᶠ[𝓝 (z x)] e'.symm := by
  have h1 : e'.target ∈ 𝓝 (z x) := by
    rw [he' hx']
    exact e'.open_target.mem_nhds (e'.map_source hx')
  have h2 : ∀ᶠ w in 𝓝 (z x), e'.symm w ∈ e.source := by
    have hc := e'.continuousAt_symm (e'.map_source hx')
    rw [← he' hx'] at hc
    have hs : e.source ∈ 𝓝 (e'.symm (z x)) := by
      rw [he' hx', e'.left_inv hx']
      exact e.open_source.mem_nhds hx
    exact hc hs
  filter_upwards [h1, h2] with w hw1 hw2
  have h3 : e (e'.symm w) = w := by
    rw [← he hw2, he' (e'.map_target hw1), e'.right_inv hw1]
  calc e.symm w = e.symm (e (e'.symm w)) := by rw [h3]
    _ = e'.symm w := e.left_inv hw2

private theorem db_eq_wdb_of_mem_chart_source (n : ℕ) {M : Type*} [TopologicalSpace M] (z : M → V n)
    {e : OpenPartialHomeomorph M (V n)} (he : IsChart n z e) (j : Fin n) (f : M → ℂ) {x : M}
    (hx : x ∈ e.source) : db n z j f x = wdb n j (f ∘ e.symm) (z x) := by
  have hex : ∃ e : OpenPartialHomeomorph M (V n), IsChart n z e ∧ x ∈ e.source := ⟨e, he, hx⟩
  unfold db
  rw [dif_pos hex]
  have hspec := Classical.choose_spec hex
  have heq : (f ∘ (Classical.choose hex).symm) =ᶠ[𝓝 (z x)] (f ∘ e.symm) :=
    (chart_symm_eventuallyEq_of_mem_sources n z hspec.1 he hspec.2 hx).fun_comp f
  unfold wdb
  rw [heq.fderiv_eq]

private theorem continuous_db_of_smooth (n : ℕ) {M : Type*} [TopologicalSpace M] (z : M → V n)
    (hz : IsLocalHomeomorph z) (j : Fin n) (φ : M → ℂ) (hφ : Smooth n z φ) :
    Continuous (db n z j φ) := by
  rw [continuous_iff_continuousAt]
  intro x
  obtain ⟨e, hxe, he⟩ := hz x
  have hc : IsChart n z e := fun y _ => by rw [he]
  have hsm := hφ e hc
  have hfd : ContinuousOn (fun w => fderiv ℝ (φ ∘ e.symm) w) e.target :=
    hsm.continuousOn_fderiv_of_isOpen e.open_target (by simp)
  have hw : ContinuousOn (wdb n j (φ ∘ e.symm)) e.target := by
    unfold wdb
    exact ((hfd.clm_apply continuousOn_const).add
      (continuousOn_const.mul (hfd.clm_apply continuousOn_const))).div_const 2
  have hat : ContinuousAt (fun y => wdb n j (φ ∘ e.symm) (e y)) x :=
    (hw.continuousAt (e.open_target.mem_nhds (e.map_source hxe))).comp (e.continuousAt hxe)
  refine hat.congr ?_
  filter_upwards [e.open_source.mem_nhds hxe] with y hy
  rw [db_eq_wdb_of_mem_chart_source n z hc j φ hy, hc hy]

private theorem db_eq_zero_of_not_mem_tsupport (n : ℕ) {M : Type*} [TopologicalSpace M] (z : M → V n)
    (hz : IsLocalHomeomorph z) (j : Fin n) (φ : M → ℂ) {x : M} (hx : x ∉ tsupport φ) :
    db n z j φ x = 0 := by
  obtain ⟨e, hxe, he⟩ := hz x
  have hc : IsChart n z e := fun y _ => by rw [he]
  rw [db_eq_wdb_of_mem_chart_source n z hc j φ hxe]
  have h0 : (φ ∘ e.symm) =ᶠ[𝓝 (z x)] fun _ => (0 : ℂ) := by
    have h1 : φ =ᶠ[𝓝 x] 0 := notMem_tsupport_iff_eventuallyEq.mp hx
    have hcont : Filter.Tendsto e.symm (𝓝 (e x)) (𝓝 x) := by
      have h2 := e.continuousAt_symm (e.map_source hxe)
      rwa [ContinuousAt, e.left_inv hxe] at h2
    rw [hc hxe]
    exact hcont.eventually h1
  unfold wdb
  rw [h0.fderiv_eq]
  simp

private theorem vol_lt_infty_of_isCompact (n : ℕ) {M : Type*} [TopologicalSpace M] [T2Space M]
    [MeasurableSpace M] [BorelSpace M] (z : M → V n) (hz : IsLocalHomeomorph z)
    (K : Set M) (hK : IsCompact K) : vol n z K < ⊤ := by
  classical
  unfold vol
  split_ifs with hadd
  · rw [Measure.ofMeasurable_apply _ hK.measurableSet]
    show volFun n z K < ⊤
    choose e hxe he using fun x => hz x
    obtain ⟨t, ht⟩ := hK.elim_finite_subcover (fun x => (e x).source) (fun x => (e x).open_source)
      (fun x _ => Set.mem_iUnion.mpr ⟨x, hxe x⟩)
    have hbound : ∀ y, (((K ∩ z ⁻¹' {y}).encard : ℕ∞) : ℝ≥0∞) ≤
        (z '' K).indicator (fun _ => (t.card : ℝ≥0∞)) y := by
      intro y
      by_cases hy : y ∈ z '' K
      · rw [Set.indicator_of_mem hy]
        have hcov : ∀ p, ∃ x, p ∈ K → x ∈ t ∧ p ∈ (e x).source := fun p => by
          by_cases hp : p ∈ K
          · obtain ⟨x, hx⟩ : ∃ x ∈ t, p ∈ (e x).source := by simpa using ht hp
            exact ⟨x, fun _ => hx⟩
          · exact ⟨p, fun h => absurd h hp⟩
        choose g hg using hcov
        have key : (K ∩ z ⁻¹' {y}).encard ≤ (t : Set M).encard := by
          refine Set.encard_le_encard_of_injOn (f := g) ?_ ?_
          · intro p hp
            exact (hg p hp.1).1
          · intro p hp p' hp' hpp'
            have h1 := (hg p hp.1).2
            have h2 := (hg p' hp'.1).2
            rw [hpp'] at h1
            have e1 : z p = y := hp.2
            have e2 : z p' = y := hp'.2
            have hzp : z p = z p' := e1.trans e2.symm
            rw [he (g p')] at hzp
            exact (e (g p')).injOn h1 h2 hzp
        rw [Set.encard_coe_eq_coe_finsetCard] at key
        exact_mod_cast key
      · have hem : K ∩ z ⁻¹' {y} = ∅ := by
          ext p
          simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff,
            Set.mem_empty_iff_false, iff_false]
          rintro ⟨hp, hpy⟩
          exact hy ⟨p, hp, hpy⟩
        rw [hem]
        simp
    have hKc : IsCompact (z '' K) := hK.image hz.continuous
    calc volFun n z K = ∫⁻ y, (((K ∩ z ⁻¹' {y}).encard : ℕ∞) : ℝ≥0∞) := rfl
      _ ≤ ∫⁻ y, (z '' K).indicator (fun _ => (t.card : ℝ≥0∞)) y := lintegral_mono hbound
      _ = t.card * volume (z '' K) := lintegral_indicator_const hKc.measurableSet _
      _ < ⊤ := ENNReal.mul_lt_top (by simp) hKc.measure_lt_top
  · simp

theorem lintegral_db_test_lt_top (n : ℕ) {M : Type*} [TopologicalSpace M] [T2Space M]
    [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M] (z : M → V n)
    (hz : IsLocalHomeomorph z) (ψ : M → ℝ) (hψ : Continuous ψ) (φ : M → ℂ)
    (hφ : IsTest n z φ) (j : Fin n) :
    ∫⁻ x, ENNReal.ofReal (‖db n z j φ x‖ ^ 2 * Real.exp (ψ x)) ∂vol n z < ⊤ := by
  have hdb := continuous_db_of_smooth n z hz j φ hφ.1
  have hK : IsCompact (tsupport φ) := hφ.2
  have hfc : ContinuousOn (fun x => ‖db n z j φ x‖ ^ 2 * Real.exp (ψ x)) (tsupport φ) :=
    ((hdb.norm.pow 2).mul (Real.continuous_exp.comp hψ)).continuousOn
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hfc
  have hle : ∀ x, ENNReal.ofReal (‖db n z j φ x‖ ^ 2 * Real.exp (ψ x)) ≤
      (tsupport φ).indicator (fun _ => ENNReal.ofReal C) x := by
    intro x
    by_cases hx : x ∈ tsupport φ
    · rw [Set.indicator_of_mem hx]
      apply ENNReal.ofReal_le_ofReal
      have h := hC x hx
      rw [Real.norm_eq_abs] at h
      exact (le_abs_self _).trans h
    · rw [db_eq_zero_of_not_mem_tsupport n z hz j φ hx]
      simp
  calc ∫⁻ x, ENNReal.ofReal (‖db n z j φ x‖ ^ 2 * Real.exp (ψ x)) ∂vol n z
      ≤ ∫⁻ x, (tsupport φ).indicator (fun _ => ENNReal.ofReal C) x ∂vol n z := lintegral_mono hle
    _ = ENNReal.ofReal C * vol n z (tsupport φ) := lintegral_indicator_const hK.measurableSet _
    _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top (vol_lt_infty_of_isCompact n z hz _ hK)

theorem integral_holo_mul_db (n : ℕ) {M : Type*} [TopologicalSpace M] [T2Space M]
    [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M] (z : M → V n)
    (hz : IsLocalHomeomorph z) (F : M → ℂ) (hF : Holo n z F) (φ : M → ℂ) (hφ : IsTest n z φ)
    (j : Fin n) : ∫ x, F x * db n z j φ x ∂vol n z = 0 := by
  have h := integral_db_mul n z hz j F φ (Smooth.ck n z 1 F (Holo.smooth n z F hF))
    (Smooth.ck n z 1 φ hφ.1) hφ.2
  have h0 : (fun x => db n z j F x * φ x) = fun _ => 0 :=
    funext fun x => by simp [Holo.db_eq_zero n z F hF j x]
  rw [h0, integral_zero] at h
  exact neg_eq_zero.mp h.symm

theorem sq_eLpNorm_two {α : Type*} [MeasurableSpace α] (μ : Measure α) (g : α → ℂ) :
    eLpNorm g 2 μ ^ 2 = ∫⁻ x, ‖g x‖ₑ ^ 2 ∂μ := by
  have h := MeasureTheory.eLpNorm_nnreal_pow_eq_lintegral (f := g) (μ := μ) (p := (2 : NNReal)) two_ne_zero
  norm_num at h
  simpa [ENNReal.rpow_two] using h

end

end ReciprocityTheory.L2DbarEstimates.F
