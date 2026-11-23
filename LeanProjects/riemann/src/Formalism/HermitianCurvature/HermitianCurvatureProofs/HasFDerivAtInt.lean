import Formalism.HermitianCurvature.HermitianCurvatureProofs.DifferentiableAtOfPuncturedSmooth
import Formalism.HermitianCurvature.HermitianCurvatureProofs.BasePointInChart

open MeasureTheory Filter Topology
open scoped ContDiff ComplexConjugate

noncomputable section

namespace Formalism.FourierDecayAlt.P.SliceIntegralLemmas

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P.LevelPointCoordinates

section fam

variable {X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X] [MeasurableSpace X]
  [BorelSpace X]
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

def UX (X : Type) [TopologicalSpace X] : Set (X × ℂ) := Set.univ ×ˢ {τ : ℂ | τ ≠ 0}

theorem isOpen_UX : IsOpen (UX X) := isOpen_univ.prod isOpen_ne_zero_complex

def Good (Φ : X → V1 E) : Prop :=
  ContDiffOn ℝ ∞ (fun q : X × ℂ => (Φ q.1 : ℂ → E) q.2) (UX X) ∧
    ∀ K : Set ℂ, IsCompact K → K ⊆ {τ | τ ≠ 0} →
      ∃ C : Set X, IsCompact C ∧ ∀ v, v ∉ C → ∀ τ ∈ K, (Φ v : ℂ → E) τ = 0

def IsInt (μ : Measure X) (ℓ : X → E →L[ℂ] E) (Φ : X → V1 E) (f : V1 E) : Prop :=
  ∀ τ : ℂ, τ ≠ 0 → (f : ℂ → E) τ = ∫ v, ℓ v ((Φ v : ℂ → E) τ) ∂μ

theorem good_cont_at {Φ : X → V1 E} (h : Good Φ) {τ : ℂ} (hτ : τ ≠ 0) :
    Continuous (fun v => (Φ v : ℂ → E) τ) :=
  h.1.continuousOn.comp_continuous (continuous_id.prodMk continuous_const) fun _ => ⟨Set.mem_univ _, hτ⟩

theorem partial_fderiv {Φ : X → V1 E} (h : Good Φ) (v : X) {τ : ℂ} (hτ : τ ≠ 0) :
    fderiv ℝ (Φ v : ℂ → E) τ =
      (fderiv ℝ (fun q : X × ℂ => (Φ q.1 : ℂ → E) q.2) (v, τ)).comp (ContinuousLinearMap.inr ℝ X ℂ) := by
  have hd : DifferentiableAt ℝ (fun q : X × ℂ => (Φ q.1 : ℂ → E) q.2) (v, τ) :=
    (h.1.differentiableOn (by simp)).differentiableAt (isOpen_UX.mem_nhds ⟨Set.mem_univ _, hτ⟩)
  have hi : HasFDerivAt (fun t : ℂ => (v, t)) (ContinuousLinearMap.inr ℝ X ℂ) τ := hasFDerivAt_prodMk_right v τ
  exact (hd.hasFDerivAt.comp τ hi).fderiv

theorem fd_contOn {Φ : X → V1 E} (h : Good Φ) :
    ContinuousOn (fun q : X × ℂ => fderiv ℝ (Φ q.1 : ℂ → E) q.2) (UX X) := by
  have h1 : ContinuousOn (fun q : X × ℂ =>
      (fderiv ℝ (fun q : X × ℂ => (Φ q.1 : ℂ → E) q.2) q).comp (ContinuousLinearMap.inr ℝ X ℂ)) (UX X) :=
    (h.1.continuousOn_fderiv_of_isOpen isOpen_UX (by simp)).clm_comp continuousOn_const
  exact h1.congr fun q hq => partial_fderiv h q.1 hq.2

theorem cd_partial {Φ : X → V1 E} (h : Good Φ) (w : ℂ) :
    ContDiffOn ℝ ∞ (fun q : X × ℂ => fderiv ℝ (Φ q.1 : ℂ → E) q.2 w) (UX X) := by
  have h1 : ContDiffOn ℝ ∞ (fun q : X × ℂ =>
      (fderiv ℝ (fun q : X × ℂ => (Φ q.1 : ℂ → E) q.2) q) (ContinuousLinearMap.inr ℝ X ℂ w)) (UX X) :=
    (h.1.fderiv_of_isOpen isOpen_UX (by simp)).clm_apply contDiffOn_const
  refine h1.congr fun q hq => ?_
  rw [partial_fderiv h q.1 hq.2]
  rfl

theorem fderiv_zero_of {Φ : X → V1 E} (h : Good Φ) {K : Set ℂ} (hK : IsCompact K) (hK0 : K ⊆ {τ | τ ≠ 0}) :
    ∃ C : Set X, IsCompact C ∧ ∀ v, v ∉ C → ∀ τ ∈ K, fderiv ℝ (Φ v : ℂ → E) τ = 0 := by
  obtain ⟨L, hL, hKL, hLU⟩ := exists_compact_between hK isOpen_ne_zero_complex hK0
  obtain ⟨C, hC, hz⟩ := h.2 L hL hLU
  refine ⟨C, hC, fun v hv τ hτ => ?_⟩
  have hev : (Φ v : ℂ → E) =ᶠ[𝓝 τ] fun _ => (0 : E) :=
    Filter.eventually_of_mem (isOpen_interior.mem_nhds (hKL hτ)) fun t ht => hz v hv t (interior_subset ht)
  rw [hev.fderiv_eq]
  exact fderiv_const_apply _

section int

variable (μ : Measure X) [IsFiniteMeasureOnCompacts μ] (ℓ : X → E →L[ℂ] E)

theorem good_int {Φ : X → V1 E} (h : Good Φ) (hℓ : Continuous ℓ) {τ : ℂ} (hτ : τ ≠ 0) :
    Integrable (fun v => ℓ v ((Φ v : ℂ → E) τ)) μ := by
  obtain ⟨C, hC, hz⟩ := h.2 {τ} isCompact_singleton (Set.singleton_subset_iff.2 hτ)
  refine Continuous.integrable_of_hasCompactSupport (hℓ.clm_apply (good_cont_at h hτ)) ?_
  refine HasCompactSupport.intro hC fun v hv => ?_
  rw [hz v hv τ rfl, map_zero]

theorem fd_int {Φ : X → V1 E} (h : Good Φ) (hℓ : Continuous ℓ) {τ : ℂ} (hτ : τ ≠ 0) (w : ℂ) :
    Integrable (fun v => ℓ v (fderiv ℝ (Φ v : ℂ → E) τ w)) μ := by
  obtain ⟨C, hC, hz⟩ := fderiv_zero_of h isCompact_singleton (Set.singleton_subset_iff.2 hτ)
  have hc : Continuous (fun v => fderiv ℝ (Φ v : ℂ → E) τ) :=
    (fd_contOn h).comp_continuous (continuous_id.prodMk continuous_const) fun _ => ⟨Set.mem_univ _, hτ⟩
  refine Continuous.integrable_of_hasCompactSupport (hℓ.clm_apply (hc.clm_apply continuous_const)) ?_
  refine HasCompactSupport.intro hC fun v hv => ?_
  rw [hz v hv τ rfl]; simp

theorem rs_cont (hℓ : Continuous ℓ) : Continuous (fun v => (ℓ v).restrictScalars ℝ) :=
  (ContinuousLinearMap.restrictScalarsL ℂ E E ℝ ℝ).continuous.comp hℓ

theorem hasFDerivAt_int {Φ : X → V1 E} (h : Good Φ) (hℓ : Continuous ℓ) {τ0 : ℂ} (hτ0 : τ0 ≠ 0) :
    HasFDerivAt (fun τ => ∫ v, ℓ v ((Φ v : ℂ → E) τ) ∂μ)
      (∫ v, ((ℓ v).restrictScalars ℝ).comp (fderiv ℝ (Φ v : ℂ → E) τ0) ∂μ) τ0 := by
  have hn : 0 < ‖τ0‖ := norm_pos_iff.2 hτ0
  set r := ‖τ0‖ / 2 with hr
  have hr0 : 0 < r := by rw [hr]; positivity
  have hK : IsCompact (Metric.closedBall τ0 r) := isCompact_closedBall _ _
  have hK0 : Metric.closedBall τ0 r ⊆ {τ | τ ≠ 0} := by
    intro τ hτ
    show τ ≠ 0
    rintro rfl
    rw [Metric.mem_closedBall, dist_zero_left] at hτ
    linarith
  have hB : ∀ τ ∈ Metric.ball τ0 r, τ ≠ 0 := fun τ hτ => hK0 (Metric.ball_subset_closedBall hτ)
  obtain ⟨C, hC, hz⟩ := fderiv_zero_of h hK hK0
  obtain ⟨Mf, hMf⟩ := (hC.prod hK).exists_bound_of_continuousOn
    ((fd_contOn h).mono fun q hq => ⟨Set.mem_univ _, hK0 hq.2⟩)
  obtain ⟨Ml, hMl⟩ := hC.exists_bound_of_continuousOn hℓ.continuousOn
  have hc0 : Continuous (fun v => fderiv ℝ (Φ v : ℂ → E) τ0) :=
    (fd_contOn h).comp_continuous (continuous_id.prodMk continuous_const) fun _ => ⟨Set.mem_univ _, hτ0⟩
  refine hasFDerivAt_integral_of_dominated_of_fderiv_le (μ := μ) (𝕜 := ℝ)
    (F := fun τ v => ℓ v ((Φ v : ℂ → E) τ))
    (F' := fun τ v => ((ℓ v).restrictScalars ℝ).comp (fderiv ℝ (Φ v : ℂ → E) τ))
    (bound := Set.indicator C fun _ => Ml * Mf) (Metric.ball_mem_nhds τ0 hr0) ?_ (good_int μ ℓ h hℓ hτ0) ?_ ?_ ?_ ?_
  · filter_upwards [Metric.ball_mem_nhds τ0 hr0] with τ hτ
    exact (hℓ.clm_apply (good_cont_at h (hB τ hτ))).aestronglyMeasurable
  · exact ((rs_cont ℓ hℓ).clm_comp hc0).aestronglyMeasurable
  · refine Filter.Eventually.of_forall fun v τ hτ => ?_
    by_cases hv : v ∈ C
    · rw [Set.indicator_of_mem hv]
      have h1 := hMl v hv
      have h2 := hMf (v, τ) ⟨hv, Metric.ball_subset_closedBall hτ⟩
      calc ‖((ℓ v).restrictScalars ℝ).comp (fderiv ℝ (Φ v : ℂ → E) τ)‖
          ≤ ‖(ℓ v).restrictScalars ℝ‖ * ‖fderiv ℝ (Φ v : ℂ → E) τ‖ := ContinuousLinearMap.opNorm_comp_le _ _
        _ = ‖ℓ v‖ * ‖fderiv ℝ (Φ v : ℂ → E) τ‖ := by rw [ContinuousLinearMap.norm_restrictScalars]
        _ ≤ Ml * Mf := mul_le_mul h1 h2 (norm_nonneg _) ((norm_nonneg _).trans h1)
    · rw [Set.indicator_of_notMem hv, hz v hv τ (Metric.ball_subset_closedBall hτ),
        ContinuousLinearMap.comp_zero, norm_zero]
  · exact (continuousOn_const.integrableOn_compact hC).integrable_indicator hC.measurableSet
  · refine Filter.Eventually.of_forall fun v τ hτ => ?_
    exact ((ℓ v).restrictScalars ℝ).hasFDerivAt.comp τ (differentiableAt_of_punctured_smooth (Φ v).2 (hB τ hτ)).hasFDerivAt

theorem fderiv_int {Φ : X → V1 E} (h : Good Φ) (hℓ : Continuous ℓ) {f : V1 E} (hf : IsInt μ ℓ Φ f) {τ0 : ℂ}
    (hτ0 : τ0 ≠ 0) (w : ℂ) :
    fderiv ℝ (f : ℂ → E) τ0 w = ∫ v, ℓ v (fderiv ℝ (Φ v : ℂ → E) τ0 w) ∂μ := by
  have hev : (f : ℂ → E) =ᶠ[𝓝 τ0] fun τ => ∫ v, ℓ v ((Φ v : ℂ → E) τ) ∂μ :=
    Filter.eventually_of_mem (isOpen_ne_zero_complex.mem_nhds hτ0) fun τ hτ => hf τ hτ
  rw [hev.fderiv_eq, (hasFDerivAt_int μ ℓ h hℓ hτ0).fderiv]
  have hc0 : Continuous (fun v => fderiv ℝ (Φ v : ℂ → E) τ0) :=
    (fd_contOn h).comp_continuous (continuous_id.prodMk continuous_const) fun _ => ⟨Set.mem_univ _, hτ0⟩
  obtain ⟨C, hC, hz⟩ := fderiv_zero_of h isCompact_singleton (Set.singleton_subset_iff.2 hτ0)
  have hI : Integrable (fun v => ((ℓ v).restrictScalars ℝ).comp (fderiv ℝ (Φ v : ℂ → E) τ0)) μ := by
    refine Continuous.integrable_of_hasCompactSupport ((rs_cont ℓ hℓ).clm_comp hc0) ?_
    refine HasCompactSupport.intro hC fun v hv => ?_
    rw [hz v hv τ0 rfl, ContinuousLinearMap.comp_zero]
  rw [ContinuousLinearMap.integral_apply hI]
  rfl

theorem dz_int {Φ : X → V1 E} (h : Good Φ) (hℓ : Continuous ℓ) {f : V1 E} (hf : IsInt μ ℓ Φ f) {τ0 : ℂ}
    (hτ0 : τ0 ≠ 0) : PBP.dz (f : ℂ → E) τ0 = ∫ v, ℓ v (PBP.dz (Φ v : ℂ → E) τ0) ∂μ := by
  unfold PBP.dz
  have hI2 : Integrable (fun v => Complex.I • ℓ v (fderiv ℝ (Φ v : ℂ → E) τ0 Complex.I)) μ :=
    (fd_int μ ℓ h hℓ hτ0 Complex.I).smul Complex.I
  rw [fderiv_int μ ℓ h hℓ hf hτ0, fderiv_int μ ℓ h hℓ hf hτ0, ← integral_smul, ← integral_sub
    (fd_int μ ℓ h hℓ hτ0 1) hI2, ← integral_smul]
  congr 1
  funext v
  rw [map_smul, map_sub, map_smul]

theorem dzb_int {Φ : X → V1 E} (h : Good Φ) (hℓ : Continuous ℓ) {f : V1 E} (hf : IsInt μ ℓ Φ f) {τ0 : ℂ}
    (hτ0 : τ0 ≠ 0) : PBP.dzb (f : ℂ → E) τ0 = ∫ v, ℓ v (PBP.dzb (Φ v : ℂ → E) τ0) ∂μ := by
  unfold PBP.dzb
  have hI2 : Integrable (fun v => Complex.I • ℓ v (fderiv ℝ (Φ v : ℂ → E) τ0 Complex.I)) μ :=
    (fd_int μ ℓ h hℓ hτ0 Complex.I).smul Complex.I
  rw [fderiv_int μ ℓ h hℓ hf hτ0, fderiv_int μ ℓ h hℓ hf hτ0, ← integral_smul, ← integral_add
    (fd_int μ ℓ h hℓ hτ0 1) hI2, ← integral_smul]
  congr 1
  funext v
  rw [map_smul, map_add, map_smul]

end int

end fam

end Formalism.FourierDecayAlt.P.SliceIntegralLemmas
