import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.GelfandFlags.IntSmooth

noncomputable section

open MeasureTheory Set Filter
open scoped ContDiff Topology

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace GlobalTheory.CompanionTheory.ParamInt

variable {X : Type} [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
  [SecondCountableTopology X] {ν : Measure X} [IsFiniteMeasureOnCompacts ν]
  {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem continuousOn_of_iteratedFDeriv_zero {W : Type} [NormedAddCommGroup W] [NormedSpace ℝ W]
    {U : Set E} {F : X → E → W}
    (h : ContinuousOn (fun p : X × E => iteratedFDeriv ℝ 0 (F p.1) p.2) (univ ×ˢ U)) :
    ContinuousOn (fun p : X × E => F p.1 p.2) (univ ×ˢ U) := by
  have e : (fun p : X × E => F p.1 p.2) =
      fun p => ContinuousMultilinearMap.apply ℝ (fun _ : Fin 0 => E) W (fun _ => 0)
        (iteratedFDeriv ℝ 0 (F p.1) p.2) := by
    funext p; simp
  rw [e]
  exact (ContinuousLinearMap.continuous _).comp_continuousOn h

theorem continuousOn_iteratedFDeriv_fderiv {W : Type} [NormedAddCommGroup W] [NormedSpace ℝ W]
    {U : Set E} {F : X → E → W} (m : ℕ)
    (h : ContinuousOn (fun p : X × E => iteratedFDeriv ℝ (m + 1) (F p.1) p.2) (univ ×ˢ U)) :
    ContinuousOn (fun p : X × E => iteratedFDeriv ℝ m (fderiv ℝ (F p.1)) p.2) (univ ×ˢ U) := by
  have e : (fun p : X × E => iteratedFDeriv ℝ m (fderiv ℝ (F p.1)) p.2) =
      fun p : X × E => continuousMultilinearCurryRightEquiv' ℝ m E W
        (iteratedFDeriv ℝ (m + 1) (F p.1) p.2) := by
    funext p
    rw [iteratedFDeriv_succ_eq_comp_right, Function.comp_apply,
      LinearIsometryEquiv.apply_symm_apply]
  rw [e]
  exact (LinearIsometryEquiv.continuous _).comp_continuousOn h

theorem integrable_bound {K : Set X} (hK : IsCompact K) (C : ℝ) :
    Integrable ((toMeasurable ν K).indicator fun _ => C) ν := by
  rw [integrable_indicator_iff (measurableSet_toMeasurable ν K)]
  refine integrableOn_const ?_
  rw [measure_toMeasurable]
  exact hK.measure_lt_top.ne

theorem le_bound {W : Type} [NormedAddCommGroup W] {K : Set X} {C : ℝ} {t : X} {w : W}
    (h1 : t ∈ K → ‖w‖ ≤ C) (h2 : t ∉ K → w = 0) :
    ‖w‖ ≤ (toMeasurable ν K).indicator (fun _ => max C 0) t := by
  by_cases ht : t ∈ K
  · rw [indicator_of_mem (subset_toMeasurable ν K ht)]
    exact (h1 ht).trans (le_max_left _ _)
  · rw [h2 ht, norm_zero]
    exact indicator_nonneg (fun _ _ => le_max_right _ _) _

theorem hasFDerivAt_integral {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
    {U : Set E} (hU : IsOpen U) {F : X → E → V}
    (h1 : ∀ t, ContDiffOn ℝ ∞ (F t) U)
    (h0 : ContinuousOn (fun p : X × E => F p.1 p.2) (univ ×ˢ U))
    (hd : ContinuousOn (fun p : X × E => fderiv ℝ (F p.1) p.2) (univ ×ˢ U))
    (h3 : ∀ x₀ ∈ U, ∃ U' ∈ 𝓝 x₀, ∃ K : Set X, IsCompact K ∧ ∀ t ∉ K, ∀ x ∈ U', F t x = 0)
    {x₀ : E} (hx : x₀ ∈ U) :
    HasFDerivAt (fun x => ∫ t, F t x ∂ν) (∫ t, fderiv ℝ (F t) x₀ ∂ν) x₀ := by
  obtain ⟨U', hU', K, hK, hz⟩ := h3 x₀ hx
  have hN : U ∩ interior U' ∈ 𝓝 x₀ := inter_mem (hU.mem_nhds hx) (interior_mem_nhds.2 hU')
  obtain ⟨r, hr, hball⟩ := Metric.nhds_basis_closedBall.mem_iff.1 hN
  have hBc : IsCompact (Metric.closedBall x₀ r) := isCompact_closedBall x₀ r
  have hKB := hK.prod hBc
  have hsub : K ×ˢ Metric.closedBall x₀ r ⊆ univ ×ˢ U :=
    fun p hp => ⟨mem_univ _, (hball hp.2).1⟩
  obtain ⟨C, hC⟩ := hKB.exists_bound_of_continuousOn (hd.mono hsub)
  obtain ⟨C₀, hC₀⟩ := hKB.exists_bound_of_continuousOn (h0.mono hsub)
  have hx₀B : x₀ ∈ Metric.closedBall x₀ r := Metric.mem_closedBall_self hr.le
  have hdz : ∀ t ∉ K, ∀ x ∈ Metric.closedBall x₀ r, fderiv ℝ (F t) x = 0 := by
    intro t ht x hxB
    have : F t =ᶠ[𝓝 x] fun _ => 0 := by
      filter_upwards [isOpen_interior.mem_nhds (hball hxB).2] with y hy
      exact hz t ht y (interior_subset hy)
    rw [this.fderiv_eq]
    simp
  have hct : ∀ x ∈ U, Continuous fun t => F t x := fun x hxU =>
    h0.comp_continuous (continuous_id.prodMk continuous_const) fun t => ⟨mem_univ _, hxU⟩
  have hcd : ∀ x ∈ U, Continuous fun t => fderiv ℝ (F t) x := fun x hxU =>
    hd.comp_continuous (continuous_id.prodMk continuous_const) fun t => ⟨mem_univ _, hxU⟩
  refine hasFDerivAt_integral_of_dominated_of_fderiv_le (F := fun x t => F t x)
    (F' := fun x t => fderiv ℝ (F t) x) (s := Metric.closedBall x₀ r)
    (bound := (toMeasurable ν K).indicator fun _ => max C 0)
    (Metric.closedBall_mem_nhds x₀ hr) ?_ ?_ ?_ ?_ (integrable_bound hK _) ?_
  · filter_upwards [hU.mem_nhds hx] with x hxU
    exact (hct x hxU).aestronglyMeasurable
  · refine Integrable.mono' (integrable_bound (ν := ν) hK (max C₀ 0))
      (hct x₀ hx).aestronglyMeasurable (ae_of_all _ fun t => ?_)
    exact le_bound (fun ht => hC₀ (t, x₀) ⟨ht, hx₀B⟩) (fun ht => hz t ht x₀ (interior_subset (hball hx₀B).2))
  · exact (hcd x₀ hx).aestronglyMeasurable
  · refine ae_of_all _ fun t x hxB => ?_
    exact le_bound (fun ht => hC (t, x) ⟨ht, hxB⟩) (fun ht => hdz t ht x hxB)
  · refine ae_of_all _ fun t x hxB => ?_
    exact (((h1 t).contDiffAt (hU.mem_nhds (hball hxB).1)).differentiableAt (by simp)).hasFDerivAt

theorem contDiffOn_integral_nat {U : Set E} (hU : IsOpen U) (m : ℕ) :
    ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V] (F : X → E → V),
      (∀ t, ContDiffOn ℝ ∞ (F t) U) →
      (∀ k : ℕ, ContinuousOn (fun p : X × E => iteratedFDeriv ℝ k (F p.1) p.2) (univ ×ˢ U)) →
      (∀ x₀ ∈ U, ∃ U' ∈ 𝓝 x₀, ∃ K : Set X, IsCompact K ∧ ∀ t ∉ K, ∀ x ∈ U', F t x = 0) →
      ContDiffOn ℝ m (fun x => ∫ t, F t x ∂ν) U := by
  have key : ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
      (F : X → E → V), (∀ t, ContDiffOn ℝ ∞ (F t) U) →
      (∀ k : ℕ, ContinuousOn (fun p : X × E => iteratedFDeriv ℝ k (F p.1) p.2) (univ ×ˢ U)) →
      (∀ x₀ ∈ U, ∃ U' ∈ 𝓝 x₀, ∃ K : Set X, IsCompact K ∧ ∀ t ∉ K, ∀ x ∈ U', F t x = 0) →
      ∀ x₀ ∈ U, HasFDerivAt (fun x => ∫ t, F t x ∂ν) (∫ t, fderiv ℝ (F t) x₀ ∂ν) x₀ := by
    intro V _ _ _ F h1 h2 h3 x₀ hx
    exact hasFDerivAt_integral hU h1 (continuousOn_of_iteratedFDeriv_zero (h2 0))
      (continuousOn_of_iteratedFDeriv_zero (F := fun t => fderiv ℝ (F t))
        (continuousOn_iteratedFDeriv_fderiv 0 (h2 1))) h3 hx
  induction m with
  | zero =>
    intro V _ _ _ F h1 h2 h3
    have : ContinuousOn (fun x => ∫ t, F t x ∂ν) U := fun x hx =>
      (key V F h1 h2 h3 x hx).continuousAt.continuousWithinAt
    have h : ContDiffOn ℝ 0 (fun x => ∫ t, F t x ∂ν) U := contDiffOn_zero.2 this
    simpa using h
  | succ m ih =>
    intro V _ _ _ F h1 h2 h3
    have hG1 : ∀ t, ContDiffOn ℝ ∞ (fderiv ℝ (F t)) U := fun t =>
      (h1 t).fderiv_of_isOpen hU (by simp)
    have hG2 : ∀ k : ℕ, ContinuousOn
        (fun p : X × E => iteratedFDeriv ℝ k (fderiv ℝ (F p.1)) p.2) (univ ×ˢ U) := fun k =>
      continuousOn_iteratedFDeriv_fderiv k (h2 (k + 1))
    have hG3 : ∀ x₀ ∈ U, ∃ U' ∈ 𝓝 x₀, ∃ K : Set X, IsCompact K ∧
        ∀ t ∉ K, ∀ x ∈ U', fderiv ℝ (F t) x = 0 := by
      intro x₀ hx
      obtain ⟨U', hU', K, hK, hz⟩ := h3 x₀ hx
      refine ⟨interior U', interior_mem_nhds.2 hU', K, hK, fun t ht x hxU => ?_⟩
      have : F t =ᶠ[𝓝 x] fun _ => 0 := by
        filter_upwards [isOpen_interior.mem_nhds hxU] with y hy
        exact hz t ht y (interior_subset hy)
      rw [this.fderiv_eq]
      simp
    have hI := ih (E →L[ℝ] V) (fun t => fderiv ℝ (F t)) hG1 hG2 hG3
    have hcast : ((m + 1 : ℕ) : WithTop ℕ∞) = (m : WithTop ℕ∞) + 1 := by norm_cast
    rw [hcast, contDiffOn_succ_iff_fderiv_of_isOpen hU]
    refine ⟨fun x hx => (key V F h1 h2 h3 x hx).differentiableAt.differentiableWithinAt,
      fun h => absurd h (by simp), ?_⟩
    exact hI.congr fun x hx => (key V F h1 h2 h3 x hx).fderiv

theorem contDiffOn_integral {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
    {U : Set E} (hU : IsOpen U) (F : X → E → V)
    (h1 : ∀ t, ContDiffOn ℝ ∞ (F t) U)
    (h2 : ∀ k : ℕ, ContinuousOn (fun p : X × E => iteratedFDeriv ℝ k (F p.1) p.2) (univ ×ˢ U))
    (h3 : ∀ x₀ ∈ U, ∃ U' ∈ 𝓝 x₀, ∃ K : Set X, IsCompact K ∧ ∀ t ∉ K, ∀ x ∈ U', F t x = 0) :
    ContDiffOn ℝ ∞ (fun x => ∫ t, F t x ∂ν) U :=
  contDiffOn_infty.2 fun m => contDiffOn_integral_nat hU m V F h1 h2 h3

theorem intSmooth : PositivityTheory.RgBcC.VC.IntSmooth := by
  intro n X _ _ _ _ ν _ V _ _ _ F h1 h2 h3
  haveI : CompleteSpace V := FiniteDimensional.complete ℂ V
  have hU : IsOpen (PositivityTheory.RgBcC.GLs n) := by
    have h : Continuous fun g : PositivityTheory.RgTw.Mat n => g.det := Continuous.matrix_det continuous_id
    exact isOpen_ne_fun h continuous_const
  exact contDiffOn_integral hU F h1 h2 h3

end GlobalTheory.CompanionTheory.ParamInt
