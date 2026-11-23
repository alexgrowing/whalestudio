import Mathlib

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ContDiff

namespace PositivityTheory.Rg.Sw.HSt.PCD

variable {F X : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X] [T2Space X] [SecondCountableTopology X]

structure Good {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] (Ω : Set F) (K : F → X → E) : Prop where
  smooth : ∀ u, ContDiffOn ℝ ∞ (K · u) Ω
  cont : ∀ N : ℕ, ContinuousOn (fun p : F × X => iteratedFDeriv ℝ N (K · p.2) p.1) (Ω ×ˢ univ)
  supp : ∀ x ∈ Ω, ∃ V : Set F, IsOpen V ∧ x ∈ V ∧ ∃ C : Set X, IsCompact C ∧ ∀ x' ∈ V, ∀ u ∉ C, K x' u = 0

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {Ω : Set F} {K : F → X → E}

theorem Good.continuousOn (hK : Good Ω K) : ContinuousOn (fun p : F × X => K p.1 p.2) (Ω ×ˢ univ) := by
  have h := (continuousMultilinearCurryFin0 ℝ F E).continuous.comp_continuousOn (hK.cont 0)
  refine h.congr fun p _ => ?_
  simp

theorem Good.dK (hΩ : IsOpen Ω) (hK : Good Ω K) : Good Ω (fun x u => fderiv ℝ (K · u) x) := by
  refine ⟨fun u => ((contDiffOn_infty_iff_fderiv_of_isOpen hΩ).1 (hK.smooth u)).2, fun N => ?_, fun x hx => ?_⟩
  · have h : ContinuousOn (fun p : F × X => (continuousMultilinearCurryRightEquiv' ℝ N F E)
        (iteratedFDeriv ℝ (N + 1) (K · p.2) p.1)) (Ω ×ˢ univ) :=
      (LinearIsometryEquiv.continuous _).comp_continuousOn (hK.cont (N + 1))
    refine h.congr fun p _ => ?_
    simp only [Function.comp_apply]
    rw [iteratedFDeriv_succ_eq_comp_right]
    simp
  · obtain ⟨V, hV, hxV, C, hC, hKV⟩ := hK.supp x hx
    refine ⟨V, hV, hxV, C, hC, fun x' hx' u hu => ?_⟩
    have : (K · u) =ᶠ[𝓝 x'] fun _ => 0 := by
      filter_upwards [hV.mem_nhds hx'] with y hy using hKV y hy u hu
    rw [this.fderiv_eq]
    simp

theorem Good.integrable (hK : Good Ω K) (ν : Measure X) [IsFiniteMeasureOnCompacts ν] {x : F} (hx : x ∈ Ω) :
    Integrable (K x) ν := by
  obtain ⟨V, -, hxV, C, hC, hKV⟩ := hK.supp x hx
  have hc : Continuous (K x) := by
    have := hK.continuousOn
    exact this.comp_continuous (Continuous.prodMk continuous_const continuous_id) (fun u => ⟨hx, mem_univ _⟩)
  exact hc.integrable_of_hasCompactSupport (HasCompactSupport.intro hC fun u hu => hKV x hxV u hu)

theorem Good.hasFDerivAt [CompleteSpace E] (hΩ : IsOpen Ω) (hK : Good Ω K) (ν : Measure X) [IsFiniteMeasureOnCompacts ν]
    {x₀ : F} (hx₀ : x₀ ∈ Ω) :
    HasFDerivAt (fun x => ∫ u, K x u ∂ν) (∫ u, fderiv ℝ (K · u) x₀ ∂ν) x₀ := by
  obtain ⟨V, hV, hxV, C, hC, hKV⟩ := hK.supp x₀ hx₀
  obtain ⟨ε, hε, hεs⟩ := Metric.isOpen_iff.1 (hΩ.inter hV) x₀ ⟨hx₀, hxV⟩
  have hK' := hK.dK hΩ
  have hc' := hK'.continuousOn
  have hcb : IsCompact (Metric.closedBall x₀ (ε / 2) ×ˢ C) := (isCompact_closedBall _ _).prod hC
  have hsub : Metric.closedBall x₀ (ε / 2) ×ˢ C ⊆ Ω ×ˢ univ := by
    intro p hp
    exact ⟨(hεs (Metric.closedBall_subset_ball (by linarith) hp.1)).1, mem_univ _⟩
  obtain ⟨M, hM⟩ := hcb.exists_bound_of_continuousOn (hc'.mono hsub)
  have hcont_u : ∀ x ∈ Ω, Continuous (K x) := fun x hx =>
    hK.continuousOn.comp_continuous (Continuous.prodMk continuous_const continuous_id) (fun u => ⟨hx, mem_univ _⟩)
  have hcont'_u : ∀ x ∈ Ω, Continuous (fun u => fderiv ℝ (K · u) x) := fun x hx =>
    hc'.comp_continuous (Continuous.prodMk continuous_const continuous_id) (fun u => ⟨hx, mem_univ _⟩)
  have hball : Metric.ball x₀ (ε / 2) ⊆ Ω ∩ V := fun y hy => hεs (Metric.ball_subset_ball (by linarith) hy)
  refine hasFDerivAt_integral_of_dominated_of_fderiv_le (μ := ν) (F := K) (F' := fun x u => fderiv ℝ (K · u) x)
    (s := Metric.ball x₀ (ε / 2))
    (bound := C.indicator fun _ => M) (Metric.ball_mem_nhds _ (by linarith)) ?_ (hK.integrable ν hx₀)
    (hcont'_u x₀ hx₀).aestronglyMeasurable ?_ ?_ ?_
  · filter_upwards [hΩ.mem_nhds hx₀] with x hx using (hcont_u x hx).aestronglyMeasurable
  · refine Filter.Eventually.of_forall fun u x hx => ?_
    by_cases hu : u ∈ C
    · rw [indicator_of_mem hu]
      exact hM (x, u) ⟨Metric.ball_subset_closedBall hx, hu⟩
    · rw [indicator_of_notMem hu]
      have : (K · u) =ᶠ[𝓝 x] fun _ => 0 := by
        filter_upwards [hV.mem_nhds (hball hx).2] with y hy using hKV y hy u hu
      rw [this.fderiv_eq]
      simp
  · exact (integrableOn_const (C := M) hC.measure_lt_top.ne).integrable_indicator hC.isClosed.measurableSet
  · refine Filter.Eventually.of_forall fun u x hx => ?_
    have hxΩ := (hball hx).1
    exact ((hK.smooth u).differentiableOn (by simp) x hxΩ).differentiableAt (hΩ.mem_nhds hxΩ) |>.hasFDerivAt

omit [NormedSpace ℝ E] in
theorem contDiffOn_nat (hΩ : IsOpen Ω) (ν : Measure X) [IsFiniteMeasureOnCompacts ν] (N : ℕ) :
    ∀ (E' : Type) [NormedAddCommGroup E'] [NormedSpace ℝ E'] [CompleteSpace E'] (K : F → X → E'), Good Ω K →
      ContDiffOn ℝ N (fun x => ∫ u, K x u ∂ν) Ω := by
  induction N with
  | zero =>
    intro E' _ _ _ K hK
    rw [Nat.cast_zero, contDiffOn_zero]
    exact fun x hx => (hK.hasFDerivAt hΩ ν hx).continuousAt.continuousWithinAt
  | succ N ih =>
    intro E' _ _ _ K hK
    rw [show ((N + 1 : ℕ) : WithTop ℕ∞) = (N : WithTop ℕ∞) + 1 by push_cast; rfl,
      contDiffOn_succ_iff_fderiv_of_isOpen hΩ]
    refine ⟨fun x hx => (hK.hasFDerivAt hΩ ν hx).differentiableAt.differentiableWithinAt, by simp, ?_⟩
    refine (ih (F →L[ℝ] E') _ (hK.dK hΩ)).congr fun x hx => ?_
    exact (hK.hasFDerivAt hΩ ν hx).fderiv

theorem contDiffOn_integral [CompleteSpace E] (hΩ : IsOpen Ω) (ν : Measure X) [IsFiniteMeasureOnCompacts ν]
    (hK : Good Ω K) : ContDiffOn ℝ ∞ (fun x => ∫ u, K x u ∂ν) Ω :=
  contDiffOn_infty.2 fun N => contDiffOn_nat hΩ ν N E K hK

theorem fderiv_integral [CompleteSpace E] (hΩ : IsOpen Ω) (ν : Measure X) [IsFiniteMeasureOnCompacts ν]
    (hK : Good Ω K) {x : F} (hx : x ∈ Ω) :
    fderiv ℝ (fun x => ∫ u, K x u ∂ν) x = ∫ u, fderiv ℝ (K · u) x ∂ν :=
  (hK.hasFDerivAt hΩ ν hx).fderiv

section Kernel

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E] {Ω : Set F}

omit [FiniteDimensional ℝ F] in
theorem slice (hΩ : IsOpen Ω) {k : F × V → E} (hk : ContDiffOn ℝ ∞ k (Ω ×ˢ univ)) (N : ℕ) {x : F} (hx : x ∈ Ω) (w : V) :
    iteratedFDeriv ℝ N (fun x => k (x, w)) x =
      (iteratedFDeriv ℝ N k (x, w)).compContinuousLinearMap (fun _ => ContinuousLinearMap.inl ℝ F V) := by
  set f' : F × V → E := fun p => k (p + (0, w))
  have hS : IsOpen (Ω ×ˢ (univ : Set V)) := hΩ.prod isOpen_univ
  have hf' : ContDiffOn ℝ ∞ f' (Ω ×ˢ univ) := by
    refine hk.comp (contDiffOn_id.add contDiffOn_const) fun p hp => ?_
    exact ⟨by simpa using hp.1, mem_univ _⟩
  have hpre : (ContinuousLinearMap.inl ℝ F V) ⁻¹' (Ω ×ˢ univ) = Ω := by ext y; simp
  have h1 := ContinuousLinearMap.iteratedFDerivWithin_comp_right (ContinuousLinearMap.inl ℝ F V) hf'
    hS.uniqueDiffOn (by rw [hpre]; exact hΩ.uniqueDiffOn) (x := x) (by simpa using hx) (i := N) (by exact_mod_cast le_top)
  rw [hpre, iteratedFDerivWithin_of_isOpen N hΩ hx, iteratedFDerivWithin_of_isOpen N hS (by simpa using hx)] at h1
  have h2 : (f' ∘ ContinuousLinearMap.inl ℝ F V) = fun x => k (x, w) := by
    funext y; simp [f']
  rw [h2] at h1
  rw [h1]
  congr 1
  have h3 := iteratedFDeriv_comp_add_right (𝕜 := ℝ) (f := k) N ((0 : F), w) (ContinuousLinearMap.inl ℝ F V x)
  simpa using h3

theorem good_of_joint (hΩ : IsOpen Ω) (k : F × V → E) (hk : ContDiffOn ℝ ∞ k (Ω ×ˢ univ)) (v : X → V)
    (hv : Continuous v) (h : X → ℂ) (hh : Continuous h)
    (hsupp : ∀ x ∈ Ω, ∃ W ∈ 𝓝 x, ∃ C : Set X, IsCompact C ∧ ∀ x' ∈ W, ∀ u ∉ C, k (x', v u) = 0) :
    Good Ω (fun x u => h u • k (x, v u)) := by
  have hsl : ∀ u, ContDiffOn ℝ ∞ (fun x => k (x, v u)) Ω := fun u =>
    hk.comp (contDiffOn_id.prodMk contDiffOn_const) fun x hx => ⟨hx, mem_univ _⟩
  refine ⟨fun u => (hsl u).const_smul (h u), fun N => ?_, fun x hx => ?_⟩
  · have hS : IsOpen (Ω ×ˢ (univ : Set V)) := hΩ.prod isOpen_univ
    have hcont : ContinuousOn (fun q : F × V => iteratedFDeriv ℝ N k q) (Ω ×ˢ univ) := by
      have := hk.continuousOn_iteratedFDerivWithin (m := N) (by exact_mod_cast le_top) hS.uniqueDiffOn
      exact this.congr fun q hq => (iteratedFDerivWithin_of_isOpen N hS hq).symm
    let hL := ContinuousMultilinearMap.compContinuousLinearMapL (𝕜 := ℝ) (F := E)
      (fun _ : Fin N => ContinuousLinearMap.inl ℝ F V)
    have hc2 : ContinuousOn (fun p : F × X => h p.2 • (hL (iteratedFDeriv ℝ N k (p.1, v p.2)))) (Ω ×ˢ univ) := by
      refine (hh.comp continuous_snd).continuousOn.smul (hL.continuous.comp_continuousOn ?_)
      exact hcont.comp (continuous_fst.prodMk (hv.comp continuous_snd)).continuousOn fun p hp => ⟨hp.1, mem_univ _⟩
    refine hc2.congr fun p hp => ?_
    have hx : p.1 ∈ Ω := hp.1
    simp only
    rw [iteratedFDeriv_const_smul_apply' ((hsl p.2).contDiffAt (hΩ.mem_nhds hx) |>.of_le (by exact_mod_cast le_top)),
      slice hΩ hk N hx (v p.2)]
    rfl
  · obtain ⟨W, hW, C, hC, hKW⟩ := hsupp x hx
    obtain ⟨W', hW'W, hW'o, hxW'⟩ := mem_nhds_iff.1 hW
    exact ⟨W', hW'o, hxW', C, hC, fun x' hx' u hu => by simp [hKW x' (hW'W hx') u hu]⟩

theorem contDiffOn_integral' (hΩ : IsOpen Ω) (ν : Measure X) [IsFiniteMeasureOnCompacts ν] (k : F × V → E)
    (hk : ContDiffOn ℝ ∞ k (Ω ×ˢ univ)) (v : X → V) (hv : Continuous v) (h : X → ℂ) (hh : Continuous h)
    (hsupp : ∀ x ∈ Ω, ∃ W ∈ 𝓝 x, ∃ C : Set X, IsCompact C ∧ ∀ x' ∈ W, ∀ u ∉ C, k (x', v u) = 0) :
    ContDiffOn ℝ ∞ (fun x => ∫ u, h u • k (x, v u) ∂ν) Ω :=
  contDiffOn_integral hΩ ν (good_of_joint hΩ k hk v hv h hh hsupp)

theorem hasFDerivAt_integral' (hΩ : IsOpen Ω) (ν : Measure X) [IsFiniteMeasureOnCompacts ν] (k : F × V → E)
    (hk : ContDiffOn ℝ ∞ k (Ω ×ˢ univ)) (v : X → V) (hv : Continuous v) (h : X → ℂ) (hh : Continuous h)
    (hsupp : ∀ x ∈ Ω, ∃ W ∈ 𝓝 x, ∃ C : Set X, IsCompact C ∧ ∀ x' ∈ W, ∀ u ∉ C, k (x', v u) = 0) {x : F} (hx : x ∈ Ω) :
    HasFDerivAt (fun x => ∫ u, h u • k (x, v u) ∂ν) (∫ u, h u • fderiv ℝ (fun x' => k (x', v u)) x ∂ν) x := by
  have hG := good_of_joint hΩ k hk v hv h hh hsupp
  have := hG.hasFDerivAt hΩ ν hx
  convert this using 2
  funext u
  have hsl : ContDiffOn ℝ ∞ (fun x => k (x, v u)) Ω :=
    hk.comp (contDiffOn_id.prodMk contDiffOn_const) fun x hx => ⟨hx, mem_univ _⟩
  have hd : DifferentiableAt ℝ (fun x => k (x, v u)) x :=
    (hsl.differentiableOn (by simp) x hx).differentiableAt (hΩ.mem_nhds hx)
  exact ((hd.hasFDerivAt.const_smul (h u)).fderiv).symm

end Kernel

end PositivityTheory.Rg.Sw.HSt.PCD
