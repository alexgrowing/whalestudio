import Mathlib

noncomputable section

open MeasureTheory Filter Topology Metric Set
open scoped ContDiff

namespace PositivityTheory.RgBcC.LfSt.ChainPf.Cact

variable {H Z : Type} [NormedAddCommGroup H] [NormedSpace ℝ H] [FiniteDimensional ℝ H]
  [NormedAddCommGroup Z] [NormedSpace ℝ Z]
  {Γ : Type} [TopologicalSpace Γ] [T2Space Γ] [MeasurableSpace Γ] [BorelSpace Γ]

def LocSupp {W : Type} [Zero W] (O : Set H) (ι : Γ → Z) (Φ : H × Z → W) : Prop :=
  ∀ x₀ ∈ O, ∃ U : Set H, IsOpen U ∧ x₀ ∈ U ∧ U ⊆ O ∧
    ∃ K : Set Γ, IsCompact K ∧ ∀ x ∈ U, ∀ y : Γ, y ∉ K → Φ (x, ι y) = 0

def pd {W : Type} [NormedAddCommGroup W] [NormedSpace ℝ W] (Φ : H × Z → W) (p : H × Z) : H →L[ℝ] W :=
  (fderiv ℝ Φ p).comp (ContinuousLinearMap.inl ℝ H Z)

variable {O : Set H} {OZ : Set Z}

theorem contDiffOn_pd {W : Type} [NormedAddCommGroup W] [NormedSpace ℝ W] {Φ : H × Z → W}
    (hO : IsOpen O) (hOZ : IsOpen OZ) (hΦ : ContDiffOn ℝ ∞ Φ (O ×ˢ OZ)) : ContDiffOn ℝ ∞ (pd Φ) (O ×ˢ OZ) := by
  have h1 : ContDiffOn ℝ ∞ (fderiv ℝ Φ) (O ×ˢ OZ) := hΦ.fderiv_of_isOpen (hO.prod hOZ) (by simp)
  exact h1.clm_comp contDiffOn_const

theorem hasFDerivAt_pd {W : Type} [NormedAddCommGroup W] [NormedSpace ℝ W] {Φ : H × Z → W}
    (hO : IsOpen O) (hOZ : IsOpen OZ) (hΦ : ContDiffOn ℝ ∞ Φ (O ×ˢ OZ)) {x : H} {z : Z} (hx : x ∈ O)
    (hz : z ∈ OZ) : HasFDerivAt (fun x' => Φ (x', z)) (pd Φ (x, z)) x := by
  have hd : DifferentiableAt ℝ Φ (x, z) :=
    (hΦ.differentiableOn (by simp)).differentiableAt ((hO.prod hOZ).mem_nhds ⟨hx, hz⟩)
  exact hd.hasFDerivAt.comp x (hasFDerivAt_prodMk_left x z)

theorem pd_eq_zero {W : Type} [NormedAddCommGroup W] [NormedSpace ℝ W] {Φ : H × Z → W}
    (hO : IsOpen O) (hOZ : IsOpen OZ) (hΦ : ContDiffOn ℝ ∞ Φ (O ×ˢ OZ)) {U : Set H} (hU : IsOpen U)
    (hUO : U ⊆ O) {z : Z} (hz : z ∈ OZ) (h0 : ∀ x ∈ U, Φ (x, z) = 0) {x : H} (hx : x ∈ U) : pd Φ (x, z) = 0 := by
  have h1 := hasFDerivAt_pd hO hOZ hΦ (hUO hx) hz
  have h2 : HasFDerivAt (fun x' => Φ (x', z)) (0 : H →L[ℝ] W) x :=
    (hasFDerivAt_const (0 : W) x).congr_of_eventuallyEq
      (eventually_of_mem (hU.mem_nhds hx) fun x' hx' => h0 x' hx')
  exact h1.unique h2

theorem locSupp_pd {W : Type} [NormedAddCommGroup W] [NormedSpace ℝ W] {Φ : H × Z → W} {ι : Γ → Z}
    (hO : IsOpen O) (hOZ : IsOpen OZ) (hι : ∀ y, ι y ∈ OZ) (hΦ : ContDiffOn ℝ ∞ Φ (O ×ˢ OZ))
    (hS : LocSupp O ι Φ) : LocSupp O ι (pd Φ) := by
  intro x₀ hx₀
  obtain ⟨U, hUo, hxU, hUO, K, hK, hKz⟩ := hS x₀ hx₀
  exact ⟨U, hUo, hxU, hUO, K, hK, fun x hx y hy =>
    pd_eq_zero hO hOZ hΦ hUo hUO (hι y) (fun x' hx' => hKz x' hx' y hy) hx⟩

theorem continuous_slice {W : Type} [TopologicalSpace W] {Φ : H × Z → W} {ι : Γ → Z} (hιc : Continuous ι)
    (hι : ∀ y, ι y ∈ OZ) (hΦ : ContinuousOn Φ (O ×ˢ OZ)) {x : H} (hx : x ∈ O) :
    Continuous fun y : Γ => Φ (x, ι y) :=
  hΦ.comp_continuous (continuous_const.prodMk hιc) fun y => ⟨hx, hι y⟩

section Int

variable (μ : Measure Γ) [IsFiniteMeasureOnCompacts μ] {ι : Γ → Z}

theorem integrable_slice {W : Type} [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
    {Φ : H × Z → W} (hιc : Continuous ι) (hι : ∀ y, ι y ∈ OZ) (hΦ : ContinuousOn Φ (O ×ˢ OZ)) {x : H} (hx : x ∈ O)
    {K : Set Γ} (hK : IsCompact K) (hKz : ∀ y : Γ, y ∉ K → Φ (x, ι y) = 0) :
    Integrable (fun y : Γ => Φ (x, ι y)) μ :=
  (continuous_slice hιc hι hΦ hx).integrable_of_hasCompactSupport (HasCompactSupport.intro hK hKz)

theorem integrable_pd {W : Type} [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
    {Φ : H × Z → W} (hO : IsOpen O) (hOZ : IsOpen OZ) (hιc : Continuous ι) (hι : ∀ y, ι y ∈ OZ)
    (hΦ : ContDiffOn ℝ ∞ Φ (O ×ˢ OZ)) (hS : LocSupp O ι Φ) {x : H} (hx : x ∈ O) :
    Integrable (fun y : Γ => pd Φ (x, ι y)) μ := by
  obtain ⟨U, hUo, hxU, hUO, K, hK, hKz⟩ := locSupp_pd hO hOZ hι hΦ hS x hx
  exact integrable_slice μ hιc hι (contDiffOn_pd hO hOZ hΦ).continuousOn hx hK fun y hy => hKz x hxU y hy

theorem hasFDerivAt_int {W : Type} [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
    {Φ : H × Z → W} (hO : IsOpen O) (hOZ : IsOpen OZ) (hιc : Continuous ι) (hι : ∀ y, ι y ∈ OZ)
    (hΦ : ContDiffOn ℝ ∞ Φ (O ×ˢ OZ)) (hS : LocSupp O ι Φ) {x₀ : H} (hx₀ : x₀ ∈ O) :
    HasFDerivAt (fun x => ∫ y : Γ, Φ (x, ι y) ∂μ) (∫ y : Γ, pd Φ (x₀, ι y) ∂μ) x₀ := by
  haveI : CompleteSpace W := FiniteDimensional.complete ℝ W
  haveI : ProperSpace H := FiniteDimensional.proper ℝ H
  obtain ⟨U, hUo, hxU, hUO, K, hK, hKz⟩ := hS x₀ hx₀
  obtain ⟨r, hr, hrU⟩ := Metric.isOpen_iff.1 hUo x₀ hxU
  have hcb : closedBall x₀ (r / 2) ⊆ U := (closedBall_subset_ball (by linarith)).trans hrU
  have hpdc : ContinuousOn (pd Φ) (O ×ˢ OZ) := (contDiffOn_pd hO hOZ hΦ).continuousOn
  have hcomp : IsCompact (closedBall x₀ (r / 2) ×ˢ K) := (isCompact_closedBall x₀ (r / 2)).prod hK
  have hcont : ContinuousOn (fun q : H × Γ => ‖pd Φ (q.1, ι q.2)‖) (closedBall x₀ (r / 2) ×ˢ K) := by
    refine (hpdc.comp (continuous_fst.prodMk (hιc.comp continuous_snd)).continuousOn ?_).norm
    intro q hq
    exact ⟨hUO (hcb hq.1), hι q.2⟩
  obtain ⟨C, hC⟩ := hcomp.exists_bound_of_continuousOn hcont
  have hKm : MeasurableSet K := hK.isClosed.measurableSet
  refine hasFDerivAt_integral_of_dominated_of_fderiv_le (𝕜 := ℝ) (F' := fun x y => pd Φ (x, ι y)) (s := ball x₀ (r / 2))
    (bound := K.indicator fun _ => C) (ball_mem_nhds x₀ (by linarith)) ?_ ?_ ?_ ?_ ?_ ?_
  · filter_upwards [hUo.mem_nhds hxU] with x hx
    exact (continuous_slice hιc hι hΦ.continuousOn (hUO hx)).aestronglyMeasurable
  · exact integrable_slice μ hιc hι hΦ.continuousOn hx₀ hK fun y hy => hKz x₀ hxU y hy
  · exact (continuous_slice hιc hι hpdc hx₀).aestronglyMeasurable
  · refine Filter.Eventually.of_forall fun y x hx => ?_
    by_cases hy : y ∈ K
    · rw [indicator_of_mem hy]
      have := hC (x, y) ⟨ball_subset_closedBall hx, hy⟩
      simpa using this
    · rw [indicator_of_notMem hy, pd_eq_zero hO hOZ hΦ hUo hUO (hι y) (fun x' hx' => hKz x' hx' y hy)
        (hcb (ball_subset_closedBall hx))]
      simp
  · exact (integrable_indicator_iff hKm).2 (integrableOn_const hK.measure_lt_top.ne)
  · exact Filter.Eventually.of_forall fun y x hx =>
      hasFDerivAt_pd hO hOZ hΦ (hUO (hcb (ball_subset_closedBall hx))) (hι y)

theorem contDiffOn_int_nat (hO : IsOpen O) (hOZ : IsOpen OZ) (hιc : Continuous ι) (hι : ∀ y, ι y ∈ OZ) :
    ∀ (m : ℕ) {W : Type} [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
    {Φ : H × Z → W}, ContDiffOn ℝ ∞ Φ (O ×ˢ OZ) → LocSupp O ι Φ →
    ContDiffOn ℝ m (fun x => ∫ y : Γ, Φ (x, ι y) ∂μ) O := by
  intro m
  induction m with
  | zero =>
    intro W _ _ _ Φ hΦ hS
    refine contDiffOn_zero.2 fun x hx => ?_
    exact (hasFDerivAt_int μ hO hOZ hιc hι hΦ hS hx).continuousAt.continuousWithinAt
  | succ m ih =>
    intro W _ _ _ Φ hΦ hS
    rw [show ((m + 1 : ℕ) : WithTop ℕ∞) = (m : WithTop ℕ∞) + 1 by push_cast; rfl,
      contDiffOn_succ_iff_fderiv_of_isOpen hO]
    refine ⟨fun x hx => (hasFDerivAt_int μ hO hOZ hιc hι hΦ hS hx).differentiableAt.differentiableWithinAt,
      fun h => absurd h (by simp), ?_⟩
    have h1 := ih (contDiffOn_pd hO hOZ hΦ) (locSupp_pd hO hOZ hι hΦ hS)
    exact h1.congr fun x hx => (hasFDerivAt_int μ hO hOZ hιc hι hΦ hS hx).fderiv

theorem contDiffOn_int {W : Type} [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
    {Φ : H × Z → W} (hO : IsOpen O) (hOZ : IsOpen OZ) (hιc : Continuous ι) (hι : ∀ y, ι y ∈ OZ)
    (hΦ : ContDiffOn ℝ ∞ Φ (O ×ˢ OZ)) (hS : LocSupp O ι Φ) :
    ContDiffOn ℝ ∞ (fun x => ∫ y : Γ, Φ (x, ι y) ∂μ) O :=
  contDiffOn_infty.2 fun m => contDiffOn_int_nat μ hO hOZ hιc hι m hΦ hS

end Int

end PositivityTheory.RgBcC.LfSt.ChainPf.Cact
