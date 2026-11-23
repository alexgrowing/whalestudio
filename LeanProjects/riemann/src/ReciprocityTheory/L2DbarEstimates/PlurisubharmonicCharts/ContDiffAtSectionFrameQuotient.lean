import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.FlatLoc
import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.FlatNull
import ReciprocityTheory.L2DbarEstimates.ChartDerivatives.HoloSmooth
import ReciprocityTheory.L2DbarEstimates.LeviForms.EventuallyDifferentiableAtOfContDiffAt

namespace ReciprocityTheory.L2DbarEstimates.Y

open MeasureTheory Filter Topology WeightedAtlas Metric
open scoped ContDiff ENNReal Pointwise Matrix

noncomputable section

universe u

variable {n : ℕ} {Y : Type u} [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y]
  [MeasurableSpace Y] [BorelSpace Y] {ι : Type*} {La : Type*} [AddCommGroup La]

theorem hyq_nsq_chart (A : WeightedAtlas n Y ι La) (la : La) (s : ι → Y → ℂ) (i : ι) (y : Y)
    (hi : y ∈ (A.chart i).source)
    (hs : s i y = A.g la i (A.pick y) y * s (A.pick y) y) :
    A.nsq la s y = ‖s i y‖ ^ 2 * Real.exp (-A.ph la i y) := by
  unfold WeightedAtlas.nsq
  have hp := A.mem_pick y
  have hg := A.g_ne la i (A.pick y) y hi hp
  have hpos : 0 < ‖A.g la i (A.pick y) y‖ ^ 2 := pow_pos (norm_pos_iff.2 hg) 2
  rw [A.ph_trans la i (A.pick y) y hi hp, hs, norm_mul, mul_pow]
  rw [show -(A.ph la i y - Real.log (‖A.g la i (A.pick y) y‖ ^ 2)) =
      -A.ph la i y + Real.log (‖A.g la i (A.pick y) y‖ ^ 2) by ring, Real.exp_add,
    Real.exp_log hpos]
  ring

theorem hyq_bdd {f : V n → ℝ} {c : V n} {r : ℝ} (hf : ContinuousOn f (closedBall c r)) :
    ∃ C : ℝ, ∀ v ∈ closedBall c r, f v ≤ C := by
  obtain ⟨C, hC⟩ := (isCompact_closedBall c r).bddAbove_image hf
  exact ⟨C, fun v hv => hC (Set.mem_image_of_mem f hv)⟩

theorem hyq_smoothFn_cont (A : WeightedAtlas n Y ι La) {f : Y → ℝ} (hf : A.SmoothFn f) :
    Continuous f := by
  rw [continuous_iff_continuousAt]
  intro y
  have hy := A.mem_pick y
  have h1 : ContinuousOn (f ∘ (A.chart (A.pick y)).symm) (A.chart (A.pick y)).target :=
    (hf (A.pick y)).continuousOn
  have h2 : ContinuousAt (f ∘ (A.chart (A.pick y)).symm) (A.chart (A.pick y) y) :=
    h1.continuousAt ((A.chart (A.pick y)).open_target.mem_nhds ((A.chart (A.pick y)).map_source hy))
  refine (h2.comp ((A.chart (A.pick y)).continuousAt hy)).congr ?_
  filter_upwards [(A.chart (A.pick y)).open_source.mem_nhds hy] with x hx
  simp [(A.chart (A.pick y)).left_inv hx]

theorem hyq_contDiffAt_of_holo {g : V n → ℂ} {U : Set (V n)} (hU : IsOpen U)
    (hg : DifferentiableOn ℂ g U) {c : V n} (hc : c ∈ U) : ContDiffAt ℝ ∞ g c :=
  (((contDiffOn_of_differentiableOn n g U hU hg).contDiffAt (hU.mem_nhds hc))).restrict_scalars ℝ

theorem hyq_contDiffAt_of_ev {g : V n → ℂ} {c : V n}
    (hg : ∀ᶠ v in 𝓝 c, DifferentiableAt ℂ g v) : ContDiffAt ℝ ∞ g c := by
  obtain ⟨U, hU, hUo, hcU⟩ := _root_.eventually_nhds_iff.1 hg
  exact hyq_contDiffAt_of_holo hUo (fun v hv => (hU v hv).differentiableWithinAt) hcU

def hyPhi (A : WeightedAtlas n Y ι La) (w0 : ι → Y → ℂ) (s : Fin n → ι → Y → ℂ)
    (σ : ι → Y → ℂ) (la : La) (ps : Y → ℝ) (y : Y) : ℝ :=
  Real.log (A.nsq A.kap (fun i y => (jz A w0 s i y).det) y) - Real.log (A.nsq (A.kap + la) σ y) +
    ps y

def sectionFrameQuotient (A : WeightedAtlas n Y ι La) (F0 σ : ι → Y → ℂ) (y : Y) : ℂ :=
  F0 (A.pick y) y / σ (A.pick y) y

variable   (A : WeightedAtlas n Y ι La) {L : La} {N : ℕ} {w : Fin N → ι → Y → ℂ} {w0 : ι → Y → ℂ}
  {s : Fin n → ι → Y → ℂ} {De : MvPolynomial (Fin n) ℂ} {la : La} {σ : ι → Y → ℂ}

theorem hyq_sigma_ne (hσ : A.IsFrameOn (A.kap + la) (A.Mset w0 s De) σ) {y : Y}
    (hy : y ∈ A.Mset w0 s De) (i : ι) (hi : y ∈ (A.chart i).source) : σ i y ≠ 0 := by
  obtain ⟨⟨_, htr⟩, hne⟩ := hσ
  rw [htr i (A.pick y) y hy hi (A.mem_pick y)]
  exact mul_ne_zero (A.g_ne _ i (A.pick y) y hi (A.mem_pick y)) (hne y hy)

theorem hyq_nsig_pos (hσ : A.IsFrameOn (A.kap + la) (A.Mset w0 s De) σ) {y : Y}
    (hy : y ∈ A.Mset w0 s De) : 0 < A.nsq (A.kap + la) σ y := by
  obtain ⟨_, hne⟩ := hσ
  unfold WeightedAtlas.nsq
  exact mul_pos (pow_pos (norm_pos_iff.2 (hne y hy)) 2) (Real.exp_pos _)

theorem hyq_nJ_pos (hD : A.D0 L w w0 s) (hF : A.Flat w0 s De) {y : Y}
    (hy : y ∈ A.Mset w0 s De) : 0 < A.nsq A.kap (fun i y => (jz A w0 s i y).det) y := by
  unfold WeightedAtlas.nsq
  have h := hF.deriv_ne y hy
  exact mul_pos (pow_pos (norm_pos_iff.2 h) 2) (Real.exp_pos _)

theorem isOpen_chart_image_mem (hD : A.D0 L w w0 s) {x : Y} (hx : x ∈ A.Mset w0 s De) (i : ι)
    (hi : x ∈ (A.chart i).source) :
    IsOpen ((A.chart i).target ∩ (A.chart i).symm ⁻¹' A.Mset w0 s De) ∧
      A.chart i x ∈ (A.chart i).target ∩ (A.chart i).symm ⁻¹' A.Mset w0 s De := by
  obtain ⟨hw0d, hw0t⟩ := hD.isSection_denom
  have hsd : ∀ k, DifferentiableOn ℂ (s k i ∘ (A.chart i).symm)
      ((A.chart i).target ∩ (A.chart i).symm ⁻¹' Set.univ) := fun k => by
    obtain ⟨h1, _⟩ := hD.sec_s k
    exact h1 i
  have hst : ∀ k, ∀ i j y, y ∈ (Set.univ : Set Y) → y ∈ (A.chart i).source →
      y ∈ (A.chart j).source → s k i y = A.g L i j y * s k j y := fun k => by
    obtain ⟨_, h2⟩ := hD.sec_s k
    exact h2
  have hT : (A.chart i).target ∩ (A.chart i).symm ⁻¹' Set.univ = (A.chart i).target := by simp
  have hw0c : ContinuousOn (w0 i ∘ (A.chart i).symm) (A.chart i).target := by
    have h := (hw0d i).continuousOn
    rwa [hT] at h
  have hsc : ∀ k, ContinuousOn (s k i ∘ (A.chart i).symm) (A.chart i).target := fun k => by
    have h := (hsd k).continuousOn
    rwa [hT] at h
  have hU1 : IsOpen ((A.chart i).target ∩ (w0 i ∘ (A.chart i).symm) ⁻¹' {0}ᶜ) :=
    hw0c.isOpen_inter_preimage (A.chart i).open_target isOpen_compl_singleton
  have hF2 : ContinuousOn (fun v => MvPolynomial.eval
      (fun k => s k i ((A.chart i).symm v) / w0 i ((A.chart i).symm v)) De)
      ((A.chart i).target ∩ (w0 i ∘ (A.chart i).symm) ⁻¹' {0}ᶜ) :=
    (MvPolynomial.continuous_eval De).comp_continuousOn (continuousOn_pi.2 fun k =>
      ((hsc k).mono Set.inter_subset_left).div (hw0c.mono Set.inter_subset_left)
        (fun v hv => hv.2))
  have hU2 := hF2.isOpen_inter_preimage hU1 (isOpen_compl_singleton (x := (0 : ℂ)))
  have key : ∀ v ∈ (A.chart i).target, ((A.chart i).symm v ∈ A.Mset w0 s De ↔
      (w0 i ((A.chart i).symm v) ≠ 0 ∧ MvPolynomial.eval
        (fun k => s k i ((A.chart i).symm v) / w0 i ((A.chart i).symm v)) De ≠ 0)) := by
    intro v hv
    have hy : (A.chart i).symm v ∈ (A.chart i).source := (A.chart i).map_target hv
    have hp := A.mem_pick ((A.chart i).symm v)
    have hg := A.g_ne L i (A.pick ((A.chart i).symm v)) ((A.chart i).symm v) hy hp
    have e0 := hw0t i (A.pick ((A.chart i).symm v)) ((A.chart i).symm v) (Set.mem_univ _) hy hp
    have ek : ∀ k, s k i ((A.chart i).symm v) / w0 i ((A.chart i).symm v) =
        s k (A.pick ((A.chart i).symm v)) ((A.chart i).symm v) /
          w0 (A.pick ((A.chart i).symm v)) ((A.chart i).symm v) := fun k => by
      rw [hst k i (A.pick ((A.chart i).symm v)) ((A.chart i).symm v) (Set.mem_univ _) hy hp, e0,
        mul_div_mul_left _ _ hg]
    simp only [ek]
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨?_, ?_⟩
      · rw [e0]
        exact mul_ne_zero hg h1
      · simpa [WeightedAtlas.zmap] using h2
    · rintro ⟨h1, h2⟩
      refine ⟨?_, ?_⟩
      · intro h0
        apply h1
        rw [e0, h0, mul_zero]
      · simpa [WeightedAtlas.zmap] using h2
  have hW : (A.chart i).target ∩ (A.chart i).symm ⁻¹' A.Mset w0 s De =
      ((A.chart i).target ∩ (w0 i ∘ (A.chart i).symm) ⁻¹' {0}ᶜ) ∩ (fun v => MvPolynomial.eval
        (fun k => s k i ((A.chart i).symm v) / w0 i ((A.chart i).symm v)) De) ⁻¹' {0}ᶜ := by
    ext v
    constructor
    · rintro ⟨hv, hm⟩
      exact ⟨⟨hv, ((key v hv).1 hm).1⟩, ((key v hv).1 hm).2⟩
    · rintro ⟨⟨hv, h1⟩, h2⟩
      exact ⟨hv, (key v hv).2 ⟨h1, h2⟩⟩
  refine ⟨by rw [hW]; exact hU2, (A.chart i).map_source hi, ?_⟩
  rw [Set.mem_preimage, (A.chart i).left_inv hi]
  exact hx

theorem hyq_sig_cd (hD : A.D0 L w w0 s) (hσ : A.IsFrameOn (A.kap + la) (A.Mset w0 s De) σ)
    {x : Y} (hx : x ∈ A.Mset w0 s De) (i : ι) (hi : x ∈ (A.chart i).source) :
    ContDiffAt ℝ ∞ (σ i ∘ (A.chart i).symm) (A.chart i x) := by
  obtain ⟨⟨hd, _⟩, _⟩ := hσ
  obtain ⟨ho, hm⟩ := isOpen_chart_image_mem A hD hx i hi
  exact hyq_contDiffAt_of_ev (Filter.eventually_of_mem (ho.mem_nhds hm) fun v hv =>
    (hd i v hv).differentiableAt (ho.mem_nhds hv))

theorem hyq_sig_holo (hD : A.D0 L w w0 s) (hσ : A.IsFrameOn (A.kap + la) (A.Mset w0 s De) σ)
    {x : Y} (hx : x ∈ A.Mset w0 s De) (i : ι) (hi : x ∈ (A.chart i).source) :
    ∀ᶠ v in 𝓝 (A.chart i x), DifferentiableAt ℂ (σ i ∘ (A.chart i).symm) v := by
  obtain ⟨⟨hd, _⟩, _⟩ := hσ
  obtain ⟨ho, hm⟩ := isOpen_chart_image_mem A hD hx i hi
  filter_upwards [ho.mem_nhds hm] with v hv
  exact (hd i v hv).differentiableAt (ho.mem_nhds hv)

theorem hyq_evM (hD : A.D0 L w w0 s) {x : Y} (hx : x ∈ A.Mset w0 s De) (i : ι)
    (hi : x ∈ (A.chart i).source) :
    ∀ᶠ v in 𝓝 (A.chart i x), v ∈ (A.chart i).target ∧ (A.chart i).symm v ∈ A.Mset w0 s De := by
  obtain ⟨ho, hm⟩ := isOpen_chart_image_mem A hD hx i hi
  filter_upwards [ho.mem_nhds hm] with v hv
  exact ⟨hv.1, hv.2⟩

theorem hyq_phi_loc (hD : A.D0 L w w0 s) (hF : A.Flat w0 s De)
    (hσ : A.IsFrameOn (A.kap + la) (A.Mset w0 s De) σ) (ps : Y → ℝ)
    {x : Y} (hx : x ∈ A.Mset w0 s De) (i : ι) (hi : x ∈ (A.chart i).source) :
    hyPhi A w0 s σ la ps =ᶠ[𝓝 x] fun y => (A.ph la i y + ps y) +
      Real.log (‖(jz A w0 s i y).det * (σ i y)⁻¹‖ ^ 2) := by
  filter_upwards [(A.chart i).open_source.mem_nhds hi, (isOpen_Mset A hD).mem_nhds hx]
    with y hyi hyM
  have hp := A.mem_pick y
  have hσne := hyq_sigma_ne A hσ hyM i hyi
  have hJne := jz_det_ne A hD hF y hyM i hyi
  have e1 := hyq_nsq_chart A _ σ i y hyi (hσ.1.2 i _ y hyM hyi hp)
  have e2 := hyq_nsq_chart A A.kap (fun i y => (jz A w0 s i y).det) i y hyi (by
    show (jz A w0 s i y).det = A.g A.kap i (A.pick y) y * (jz A w0 s (A.pick y) y).det
    rw [jz_det_trans A hD hF y hyM i (A.pick y) hyi hp, mul_comm])
  unfold hyPhi
  rw [e1, e2, A.ph_add A.kap la i y hyi, norm_mul, norm_inv, mul_pow, inv_pow,
    Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
    Real.log_mul (by positivity) (by positivity), Real.log_inv, Real.log_exp, Real.log_exp]
  ring

theorem hyq_q_cd (hD : A.D0 L w w0 s) (hF : A.Flat w0 s De)
    (hσ : A.IsFrameOn (A.kap + la) (A.Mset w0 s De) σ)
    {x : Y} (hx : x ∈ A.Mset w0 s De) (i : ι) (hi : x ∈ (A.chart i).source) :
    (∀ᶠ v in 𝓝 (A.chart i x), DifferentiableAt ℂ
      (fun v => (fderiv ℂ (A.zLoc w0 s i) v).det * (σ i ((A.chart i).symm v))⁻¹) v) ∧
    ((fun y => (jz A w0 s i y).det * (σ i y)⁻¹) ∘ (A.chart i).symm =ᶠ[𝓝 (A.chart i x)]
      fun v => (fderiv ℂ (A.zLoc w0 s i) v).det * (σ i ((A.chart i).symm v))⁻¹) ∧
    (fun v => (fderiv ℂ (A.zLoc w0 s i) v).det * (σ i ((A.chart i).symm v))⁻¹) (A.chart i x) ≠ 0 := by
  refine ⟨?_, ?_, ?_⟩
  · filter_upwards [differentiableAt_det_jz A hD hF x hx i hi, hyq_sig_holo A hD hσ hx i hi,
      hyq_evM A hD hx i hi] with v h1 h2 h3
    exact h1.mul (h2.inv (hyq_sigma_ne A hσ h3.2 i ((A.chart i).map_target h3.1)))
  · filter_upwards [(A.chart i).open_target.mem_nhds ((A.chart i).map_source hi)] with v hv
    simp only [Function.comp, jz, (A.chart i).right_inv hv]
  · simp only [(A.chart i).left_inv hi]
    exact mul_ne_zero (by simpa [jz] using jz_det_ne A hD hF x hx i hi)
      (inv_ne_zero (hyq_sigma_ne A hσ hx i hi))

theorem hyq_phi_smooth (hD : A.D0 L w w0 s) (hF : A.Flat w0 s De)
    (hσ : A.IsFrameOn (A.kap + la) (A.Mset w0 s De) σ) {ps : Y → ℝ} (hps : A.SmoothFn ps)
    {x : Y} (hx : x ∈ A.Mset w0 s De) (i : ι) (hi : x ∈ (A.chart i).source) :
    ContDiffAt ℝ ∞ (hyPhi A w0 s σ la ps ∘ (A.chart i).symm) (A.chart i x) := by
  have hloc := hyq_phi_loc A hD hF hσ ps hx i hi
  obtain ⟨hQd, hQeq, hQne⟩ := hyq_q_cd A hD hF hσ hx i hi
  have hc := (A.chart i).map_source hi
  have ht : Filter.Tendsto (A.chart i).symm (𝓝 (A.chart i x)) (𝓝 x) := by
    have h0 := (A.chart i).continuousAt_symm hc
    rwa [ContinuousAt, (A.chart i).left_inv hi] at h0
  have h1 : hyPhi A w0 s σ la ps ∘ (A.chart i).symm =ᶠ[𝓝 (A.chart i x)] fun v =>
      (A.ph la i ((A.chart i).symm v) + ps ((A.chart i).symm v)) +
        Real.log (‖(fderiv ℂ (A.zLoc w0 s i) v).det * (σ i ((A.chart i).symm v))⁻¹‖ ^ 2) := by
    filter_upwards [hloc.comp_tendsto ht, hQeq] with v e1 e2
    simp only [Function.comp_apply] at e1 e2 ⊢
    rw [e1, e2]
  refine ContDiffAt.congr_of_eventuallyEq ?_ h1
  have hph : ContDiffAt ℝ ∞ (A.ph la i ∘ (A.chart i).symm) (A.chart i x) :=
    (A.smooth_ph la i).contDiffAt ((A.chart i).open_target.mem_nhds hc)
  have hps' : ContDiffAt ℝ ∞ (ps ∘ (A.chart i).symm) (A.chart i x) :=
    (hps i).contDiffAt ((A.chart i).open_target.mem_nhds hc)
  have hQs := hyq_contDiffAt_of_ev hQd
  have hlog := (hQs.norm_sq ℝ).log (pow_ne_zero 2 (norm_ne_zero_iff.2 hQne))
  exact (hph.add hps').add hlog

theorem hyq_levi_phi (hD : A.D0 L w w0 s) (hF : A.Flat w0 s De)
    (hσ : A.IsFrameOn (A.kap + la) (A.Mset w0 s De) σ) {ps : Y → ℝ} (hps : A.SmoothFn ps)
    {x : Y} (hx : x ∈ A.Mset w0 s De) (i : ι) (hi : x ∈ (A.chart i).source) (ξ : Fin n → ℂ) :
    A.leviAt i (hyPhi A w0 s σ la ps) x ξ = A.leviAt i (fun y => A.ph la i y + ps y) x ξ := by
  obtain ⟨hqd, hqe, hqne⟩ := hyq_q_cd A hD hF hσ hx i hi
  have hc : (A.chart i).symm (A.chart i x) = x := (A.chart i).left_inv hi
  have hT := (A.chart i).open_target.mem_nhds ((A.chart i).map_source hi)
  have hq : ContDiffAt ℝ ∞ (fun v => (fderiv ℂ (A.zLoc w0 s i) v).det *
      (σ i ((A.chart i).symm v))⁻¹) (A.chart i x) :=
    ((contDiffAt_det_jz A hD hF x hx i hi).restrict_scalars ℝ).mul
      ((hyq_sig_cd A hD hσ hx i hi).inv (by simp only [Function.comp, hc]; exact hyq_sigma_ne A hσ hx i hi))
  have hf2 : ContDiffAt ℝ 2 ((fun y => A.ph la i y + ps y) ∘ (A.chart i).symm) (A.chart i x) :=
    (((A.smooth_ph la i).contDiffAt hT).add ((hps i).contDiffAt hT)).of_le (WithTop.coe_le_coe.mpr le_top)
  have hg2 : ContDiffAt ℝ 2 ((fun y => Real.log (‖(jz A w0 s i y).det * (σ i y)⁻¹‖ ^ 2)) ∘
      (A.chart i).symm) (A.chart i x) := by
    refine (((hq.norm_sq ℝ).log (by positivity)).of_le (WithTop.coe_le_coe.mpr le_top)).congr_of_eventuallyEq ?_
    filter_upwards [hqe] with v hv
    simp only [Function.comp] at hv ⊢
    rw [hv]
  have hh : ∀ᶠ v in 𝓝 (A.chart i x), DifferentiableAt ℂ
      ((fun y => (jz A w0 s i y).det * (σ i y)⁻¹) ∘ (A.chart i).symm) v := by
    filter_upwards [hqd, hqe.eventuallyEq_nhds] with v h1 h2
    exact h1.congr_of_eventuallyEq h2
  rw [leviAt_congr A i _ _ x hi (hyq_phi_loc A hD hF hσ ps hx i hi) ξ,
    leviAt_add A i (fun y => A.ph la i y + ps y)
      (fun y => Real.log (‖(jz A w0 s i y).det * (σ i y)⁻¹‖ ^ 2)) x hf2 hg2 ξ,
    leviAt_log_normSq A i (fun y => (jz A w0 s i y).det * (σ i y)⁻¹) x hi hh
      (mul_ne_zero (jz_det_ne A hD hF x hx i hi) (inv_ne_zero (hyq_sigma_ne A hσ hx i hi))) ξ,
    add_zero]

theorem hyq_nsig_smooth (hD : A.D0 L w w0 s) (hσ : A.IsFrameOn (A.kap + la) (A.Mset w0 s De) σ)
    {x : Y} (hx : x ∈ A.Mset w0 s De) (i : ι) (hi : x ∈ (A.chart i).source) :
    ContDiffAt ℝ ∞ (A.nsq (A.kap + la) σ ∘ (A.chart i).symm) (A.chart i x) := by
  have hsg := hyq_sig_cd A hD hσ hx i hi
  obtain ⟨⟨_, htr⟩, _⟩ := hσ
  obtain ⟨ho, hm⟩ := isOpen_chart_image_mem A hD hx i hi
  have hev : A.nsq (A.kap + la) σ ∘ (A.chart i).symm =ᶠ[𝓝 (A.chart i x)] fun v =>
      ‖σ i ((A.chart i).symm v)‖ ^ 2 * Real.exp (-A.ph (A.kap + la) i ((A.chart i).symm v)) := by
    filter_upwards [ho.mem_nhds hm] with v hv
    have hs' := (A.chart i).map_target hv.1
    exact hyq_nsq_chart A (A.kap + la) σ i ((A.chart i).symm v) hs'
      (htr i (A.pick ((A.chart i).symm v)) ((A.chart i).symm v) hv.2 hs' (A.mem_pick _))
  refine ContDiffAt.congr_of_eventuallyEq ?_ hev
  have hph : ContDiffAt ℝ ∞ (A.ph (A.kap + la) i ∘ (A.chart i).symm) (A.chart i x) :=
    (A.smooth_ph (A.kap + la) i).contDiffAt
      ((A.chart i).open_target.mem_nhds ((A.chart i).map_source hi))
  exact (hsg.norm_sq ℝ).mul hph.neg.exp

theorem contDiffAt_sectionFrameQuotient (hD : A.D0 L w w0 s) (hσ : A.IsFrameOn (A.kap + la) (A.Mset w0 s De) σ)
    {F0 : ι → Y → ℂ} (hF0 : A.IsSSec (A.kap + la) F0)
    {x : Y} (hx : x ∈ A.Mset w0 s De) (i : ι) (hi : x ∈ (A.chart i).source) :
    ContDiffAt ℝ ∞ (sectionFrameQuotient A F0 σ ∘ (A.chart i).symm) (A.chart i x) := by
  have h2 := hyq_sig_cd A hD hσ hx i hi
  have hne := hyq_sigma_ne A hσ hx i hi
  obtain ⟨⟨_, htr⟩, _⟩ := hσ
  obtain ⟨hF0s, hF0t⟩ := hF0
  obtain ⟨ho, hm⟩ := isOpen_chart_image_mem A hD hx i hi
  have hev : sectionFrameQuotient A F0 σ ∘ (A.chart i).symm =ᶠ[𝓝 (A.chart i x)] fun v =>
      F0 i ((A.chart i).symm v) / σ i ((A.chart i).symm v) := by
    filter_upwards [ho.mem_nhds hm] with v hv
    have hs' := (A.chart i).map_target hv.1
    have hp := A.mem_pick ((A.chart i).symm v)
    simp only [Function.comp_apply, sectionFrameQuotient]
    rw [hF0t i _ _ hs' hp, htr i _ _ hv.2 hs' hp,
      mul_div_mul_left _ _ (A.g_ne _ i _ _ hs' hp)]
  refine ContDiffAt.congr_of_eventuallyEq ?_ hev
  have h1 : ContDiffAt ℝ ∞ (F0 i ∘ (A.chart i).symm) (A.chart i x) :=
    (hF0s i).contDiffAt ((A.chart i).open_target.mem_nhds ((A.chart i).map_source hi))
  have hne' : (σ i ∘ (A.chart i).symm) (A.chart i x) ≠ 0 := by
    simpa [(A.chart i).left_inv hi] using hne
  have h3 := h1.mul (h2.inv hne')
  refine h3.congr_of_eventuallyEq (Filter.Eventually.of_forall fun v => ?_)
  simp [div_eq_mul_inv]

theorem dbar_sectionFrameQuotient (hD : A.D0 L w w0 s) (hσ : A.IsFrameOn (A.kap + la) (A.Mset w0 s De) σ)
    {F0 : ι → Y → ℂ} (hF0 : A.IsSSec (A.kap + la) F0)
    {x : Y} (hx : x ∈ A.Mset w0 s De) (i : ι) (hi : x ∈ (A.chart i).source) (ξ : Fin n → ℂ) :
    A.dbarAt i (fun _ => sectionFrameQuotient A F0 σ) x ξ = A.dbarAt i F0 x ξ / σ i x := by
  have hsh := hyq_sig_holo A hD hσ hx i hi
  have hne := hyq_sigma_ne A hσ hx i hi
  obtain ⟨⟨_, htr⟩, _⟩ := hσ
  obtain ⟨hF0s, hF0t⟩ := hF0
  obtain ⟨ho, hm⟩ := isOpen_chart_image_mem A hD hx i hi
  have hc := (A.chart i).map_source hi
  have hev : sectionFrameQuotient A F0 σ ∘ (A.chart i).symm =ᶠ[𝓝 (A.chart i x)] fun v =>
      (F0 i ∘ (A.chart i).symm) v * ((σ i ∘ (A.chart i).symm) v)⁻¹ := by
    filter_upwards [ho.mem_nhds hm] with v hv
    have hs' := (A.chart i).map_target hv.1
    have hp := A.mem_pick ((A.chart i).symm v)
    simp only [Function.comp_apply, sectionFrameQuotient]
    rw [hF0t i _ _ hs' hp, htr i _ _ hv.2 hs' hp, ← div_eq_mul_inv,
      mul_div_mul_left _ _ (A.g_ne _ i _ _ hs' hp)]
  have hne' : (σ i ∘ (A.chart i).symm) (A.chart i x) ≠ 0 := by
    simpa [(A.chart i).left_inv hi] using hne
  have hFd : DifferentiableAt ℝ (F0 i ∘ (A.chart i).symm) (A.chart i x) :=
    ((hF0s i).contDiffAt ((A.chart i).open_target.mem_nhds hc)).differentiableAt (by simp)
  have hGd : DifferentiableAt ℂ (fun v => ((σ i ∘ (A.chart i).symm) v)⁻¹) (A.chart i x) :=
    hsh.self_of_nhds.inv hne'
  have key : ∀ (j : Fin n) (F G : V n → ℂ) (c : V n), DifferentiableAt ℝ F c →
      DifferentiableAt ℂ G c → wdb n j (fun v => F v * G v) c = wdb n j F c * G c := by
    intro j F G c hF hG
    unfold wdb
    rw [fderiv_fun_mul hF (hG.restrictScalars ℝ), hG.fderiv_restrictScalars ℝ]
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul,
      ContinuousLinearMap.coe_restrictScalars', map_smul]
    linear_combination (F c * fderiv ℂ G c (bas n j) / 2) * Complex.I_mul_I
  unfold WeightedAtlas.dbarAt
  rw [Finset.sum_div]
  refine Finset.sum_congr rfl fun j _ => ?_
  show wdb n j (sectionFrameQuotient A F0 σ ∘ (A.chart i).symm) (A.chart i x) * (starRingEnd ℂ) (ξ j) =
    wdb n j (F0 i ∘ (A.chart i).symm) (A.chart i x) * (starRingEnd ℂ) (ξ j) / σ i x
  have hw1 : wdb n j (sectionFrameQuotient A F0 σ ∘ (A.chart i).symm) (A.chart i x) =
      wdb n j (fun v => (F0 i ∘ (A.chart i).symm) v * ((σ i ∘ (A.chart i).symm) v)⁻¹)
        (A.chart i x) := by
    unfold wdb
    rw [hev.fderiv_eq (𝕜 := ℝ)]
  rw [hw1, key j _ _ _ hFd hGd]
  simp only [Function.comp_apply, (A.chart i).left_inv hi]
  ring

end

end ReciprocityTheory.L2DbarEstimates.Y
