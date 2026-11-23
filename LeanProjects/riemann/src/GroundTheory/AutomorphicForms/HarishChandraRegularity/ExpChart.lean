import Mathlib
import GroundTheory.AutomorphicForms.HarishChandraRegularity.ContDiffCompCoordEquiv

namespace GroundTheory.Automorphic

open NormedSpace Set Filter Topology
open scoped ContDiff

set_option linter.unusedSectionVars false

variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [FiniteDimensional ℝ 𝔸]

theorem analyticAt_expPartialHomeomorph_symm {y : 𝔸}
    (hy : y ∈ (expPartialHomeomorph ℝ 𝔸).target) :
    AnalyticAt ℝ (expPartialHomeomorph ℝ 𝔸).symm y := by
  set e := expPartialHomeomorph ℝ 𝔸 with he
  have hs : e.symm y ∈ e.source := e.map_target hy
  have hu : IsUnit (fderiv ℝ (exp : 𝔸 → 𝔸) (e.symm y)) :=
    expPartialHomeomorph_source_subset ℝ 𝔸 hs
  obtain ⟨p, hp⟩ := exp_analytic (𝕂 := ℝ) (e.symm y)
  have hp' : HasFPowerSeriesAt e p (e.symm y) := by
    rw [he, coe_expPartialHomeomorph]; exact hp
  have h1 : p 1 = (continuousMultilinearCurryFin1 ℝ 𝔸 𝔸).symm
      ((ContinuousLinearEquiv.unitsEquiv ℝ 𝔸 hu.unit : 𝔸 ≃L[ℝ] 𝔸) : 𝔸 →L[ℝ] 𝔸) := by
    have h2 := hp.fderiv_eq
    have h3 : ((ContinuousLinearEquiv.unitsEquiv ℝ 𝔸 hu.unit : 𝔸 ≃L[ℝ] 𝔸) : 𝔸 →L[ℝ] 𝔸) =
        fderiv ℝ (exp : 𝔸 → 𝔸) (e.symm y) := by
      ext x; simp
    rw [h3, h2, LinearIsometryEquiv.symm_apply_apply]
  have := e.hasFPowerSeriesAt_symm hs hp' h1
  rw [e.right_inv hy] at this
  exact this.analyticAt

variable {G : Subgroup 𝔸ˣ} {𝔤 : Submodule ℝ 𝔸}

noncomputable def expChartProd {d : ℕ} (b : Module.Basis (Fin d) ℝ 𝔤) (X : 𝔤)
    (p : EuclideanSpace ℝ (Fin d) × ℝ) : 𝔸 :=
  exp ((coordEquiv b p.1 : 𝔤) : 𝔸) * exp (p.2 • (X : 𝔸))

noncomputable def expChartFlow {d : ℕ} (b : Module.Basis (Fin d) ℝ 𝔤) (X : 𝔤)
    (p : EuclideanSpace ℝ (Fin d) × ℝ) : EuclideanSpace ℝ (Fin d) :=
  (coordEquiv b).symm (subspaceProj 𝔤 ((expPartialHomeomorph ℝ 𝔸).symm (expChartProd b X p)))

noncomputable def expChartCoeff {d : ℕ} (b : Module.Basis (Fin d) ℝ 𝔤) (X : 𝔤)
    (x : EuclideanSpace ℝ (Fin d)) : EuclideanSpace ℝ (Fin d) :=
  fderiv ℝ (expChartFlow b X) (x, 0) (0, 1)

theorem continuous_expChartProd {d : ℕ} (b : Module.Basis (Fin d) ℝ 𝔤) (X : 𝔤) :
    Continuous (expChartProd b X) := by
  unfold expChartProd
  refine Continuous.mul ?_ ?_
  · exact (contDiff_exp ℝ 𝔸 (n := 0)).continuous.comp
      (continuous_subtype_val.comp ((coordEquiv b).continuous.comp continuous_fst))
  · exact (contDiff_exp ℝ 𝔸 (n := 0)).continuous.comp (continuous_snd.smul continuous_const)

theorem analyticAt_expChartProd {d : ℕ} (b : Module.Basis (Fin d) ℝ 𝔤) (X : 𝔤)
    (p : EuclideanSpace ℝ (Fin d) × ℝ) : AnalyticAt ℝ (expChartProd b X) p := by
  have h1 : AnalyticAt ℝ (fun q : EuclideanSpace ℝ (Fin d) × ℝ => ((coordEquiv b q.1 : 𝔤) : 𝔸)) p :=
    (𝔤.subtypeL.comp ((coordEquiv b : EuclideanSpace ℝ (Fin d) →L[ℝ] 𝔤).comp
      (ContinuousLinearMap.fst ℝ _ ℝ))).analyticAt p
  have h2 : AnalyticAt ℝ (fun q : EuclideanSpace ℝ (Fin d) × ℝ => q.2 • (X : 𝔸)) p :=
    ((ContinuousLinearMap.snd ℝ (EuclideanSpace ℝ (Fin d)) ℝ).smulRight (X : 𝔸)).analyticAt p
  have h1' := (exp_analytic (𝕂 := ℝ) _).comp h1
  have h2' := (exp_analytic (𝕂 := ℝ) _).comp h2
  exact h1'.mul h2'

theorem analyticAt_expChartFlow {d : ℕ} (b : Module.Basis (Fin d) ℝ 𝔤) (X : 𝔤)
    {p : EuclideanSpace ℝ (Fin d) × ℝ}
    (hp : expChartProd b X p ∈ (expPartialHomeomorph ℝ 𝔸).target) :
    AnalyticAt ℝ (expChartFlow b X) p := by
  have hL : AnalyticAt ℝ (fun w : 𝔸 => (coordEquiv b).symm (subspaceProj 𝔤 w))
      ((expPartialHomeomorph ℝ 𝔸).symm (expChartProd b X p)) :=
    (((coordEquiv b).symm : 𝔤 →L[ℝ] EuclideanSpace ℝ (Fin d)).comp (subspaceProj 𝔤)).analyticAt _
  have h2 : AnalyticAt ℝ ((expPartialHomeomorph ℝ 𝔸).symm ∘ expChartProd b X) p :=
    (analyticAt_expPartialHomeomorph_symm hp).comp (analyticAt_expChartProd b X p)
  exact AnalyticAt.comp (f := (expPartialHomeomorph ℝ 𝔸).symm ∘ expChartProd b X)
    (g := fun w : 𝔸 => (coordEquiv b).symm (subspaceProj 𝔤 w)) hL h2

theorem analyticOnNhd_expChartFlow {d : ℕ} (b : Module.Basis (Fin d) ℝ 𝔤) (X : 𝔤) :
    AnalyticOnNhd ℝ (expChartFlow b X) (expChartProd b X ⁻¹' (expPartialHomeomorph ℝ 𝔸).target) :=
  fun _ hp => analyticAt_expChartFlow b X hp

namespace IsExpLieAlgebra

variable (h : IsExpLieAlgebra G 𝔤)

theorem exists_ball_coordEquiv_mem_nhd {d : ℕ} (b : Module.Basis (Fin d) ℝ 𝔤) :
    ∃ r > 0, ∀ x ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin d)) r,
      ((coordEquiv b x : 𝔤) : 𝔸) ∈ h.nhd := by
  have hc : Continuous (fun x : EuclideanSpace ℝ (Fin d) => ((coordEquiv b x : 𝔤) : 𝔸)) :=
    continuous_subtype_val.comp (coordEquiv b).continuous
  have h0 : h.nhd ∈ 𝓝 ((fun x : EuclideanSpace ℝ (Fin d) => ((coordEquiv b x : 𝔤) : 𝔸)) 0) := by
    simp only [map_zero, ZeroMemClass.coe_zero]
    exact h.isOpen_nhd.mem_nhds h.zero_mem_nhd
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.1 (hc.continuousAt.preimage_mem_nhds h0)
  exact ⟨r, hr, fun x hx => hball hx⟩

theorem val_expG_mul_expG {d : ℕ} (b : Module.Basis (Fin d) ℝ 𝔤) (X : 𝔤)
    (p : EuclideanSpace ℝ (Fin d) × ℝ) :
    (((h.expG (coordEquiv b p.1) * h.expG (p.2 • X) : G) : 𝔸ˣ) : 𝔸) = expChartProd b X p := by
  simp [expChartProd]

theorem expG_expChartFlow {d : ℕ} (b : Module.Basis (Fin d) ℝ 𝔤) (X : 𝔤)
    {p : EuclideanSpace ℝ (Fin d) × ℝ} (hp : expChartProd b X p ∈ h.nhdOne) :
    h.expG (coordEquiv b (expChartFlow b X p)) = h.expG (coordEquiv b p.1) * h.expG (p.2 • X) := by
  set w : G := h.expG (coordEquiv b p.1) * h.expG (p.2 • X) with hw
  have hwv : ((w : 𝔸ˣ) : 𝔸) = expChartProd b X p := h.val_expG_mul_expG b X p
  have hwN : ((w : 𝔸ˣ) : 𝔸) ∈ h.nhdOne := hwv ▸ hp
  have hmem := h.symm_mem_lie hwN
  have e1 : coordEquiv b (expChartFlow b X p) =
      subspaceProj 𝔤 ((expPartialHomeomorph ℝ 𝔸).symm ((w : 𝔸ˣ) : 𝔸)) := by
    rw [hwv]; exact (coordEquiv b).apply_symm_apply _
  apply Subtype.ext; apply Units.ext
  rw [coe_expG, e1, subspaceProj_of_mem hmem, h.exp_symm hwN]

theorem expChartFlow_zero {d : ℕ} (b : Module.Basis (Fin d) ℝ 𝔤) (X : 𝔤)
    {x : EuclideanSpace ℝ (Fin d)} (hx : ((coordEquiv b x : 𝔤) : 𝔸) ∈ h.nhd) :
    expChartFlow b X (x, 0) = x := by
  simp only [expChartFlow, expChartProd, zero_smul, exp_zero, mul_one]
  rw [h.symm_exp hx, subspaceProj_coe, ContinuousLinearEquiv.symm_apply_apply]

theorem expChartProd_zero_mem_nhdOne {d : ℕ} (b : Module.Basis (Fin d) ℝ 𝔤) (X : 𝔤)
    {x : EuclideanSpace ℝ (Fin d)} (hx : ((coordEquiv b x : 𝔤) : 𝔸) ∈ h.nhd) :
    expChartProd b X (x, 0) ∈ h.nhdOne := by
  simp only [expChartProd, zero_smul, exp_zero, mul_one]
  exact h.exp_mem_nhdOne hx

theorem hasDerivAt_expChartFlow {d : ℕ} (b : Module.Basis (Fin d) ℝ 𝔤) (X : 𝔤)
    {x : EuclideanSpace ℝ (Fin d)} (hx : ((coordEquiv b x : 𝔤) : 𝔸) ∈ h.nhd) :
    HasDerivAt (fun t : ℝ => expChartFlow b X (x, t)) (expChartCoeff b X x) 0 := by
  have hA : AnalyticAt ℝ (expChartFlow b X) (x, 0) :=
    analyticAt_expChartFlow b X (h.nhdOne_subset_target (h.expChartProd_zero_mem_nhdOne b X hx))
  have hl : HasDerivAt (fun t : ℝ => (x, t)) ((0 : EuclideanSpace ℝ (Fin d)), (1 : ℝ)) 0 :=
    (hasDerivAt_const (0 : ℝ) x).prodMk (hasDerivAt_id 0)
  exact hA.differentiableAt.hasFDerivAt.comp_hasDerivAt (x := (0 : ℝ)) hl

theorem exists_expChart_coeff {d : ℕ} (b : Module.Basis (Fin d) ℝ 𝔤) :
    ∃ r > 0, ∃ c : 𝔤 → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d),
      (∀ X, AnalyticOnNhd ℝ (c X) (Metric.ball 0 r)) ∧
      (∀ X, c X 0 = (coordEquiv b).symm X) ∧
      ∀ (X : 𝔤) (f : G → ℂ), h.IsSmoothFun f → ∀ (g : G),
        ∀ x ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin d)) r,
          h.rightDeriv X f (g * h.expG (coordEquiv b x)) =
            fderiv ℝ (fun y => f (g * h.expG (coordEquiv b y))) x (c X x) := by
  obtain ⟨r, hr, hball⟩ := h.exists_ball_coordEquiv_mem_nhd b
  refine ⟨r, hr, expChartCoeff b, ?_, ?_, ?_⟩
  ·
    intro X x hx
    have hS : (x, (0 : ℝ)) ∈ expChartProd b X ⁻¹' (expPartialHomeomorph ℝ 𝔸).target :=
      h.nhdOne_subset_target (h.expChartProd_zero_mem_nhdOne b X (hball x hx))
    have hD := (analyticOnNhd_expChartFlow b X).fderiv (𝕜 := ℝ) _ hS
    have hinl : AnalyticAt ℝ (fun y : EuclideanSpace ℝ (Fin d) => (y, (0 : ℝ))) x :=
      (ContinuousLinearMap.inl ℝ (EuclideanSpace ℝ (Fin d)) ℝ).analyticAt x
    have hD' : AnalyticAt ℝ (fun y : EuclideanSpace ℝ (Fin d) =>
        fderiv ℝ (expChartFlow b X) (y, 0)) x :=
      AnalyticAt.comp (g := fderiv ℝ (expChartFlow b X))
        (f := fun y : EuclideanSpace ℝ (Fin d) => (y, (0 : ℝ))) hD hinl
    have hap := (ContinuousLinearMap.apply ℝ (EuclideanSpace ℝ (Fin d))
      ((0 : EuclideanSpace ℝ (Fin d)), (1 : ℝ))).analyticAt (fderiv ℝ (expChartFlow b X) (x, 0))
    exact AnalyticAt.comp (f := fun y : EuclideanSpace ℝ (Fin d) => fderiv ℝ (expChartFlow b X) (y, 0))
      hap hD'
  ·
    intro X
    have h0 : ((coordEquiv b (0 : EuclideanSpace ℝ (Fin d)) : 𝔤) : 𝔸) ∈ h.nhd := by
      simp only [map_zero, ZeroMemClass.coe_zero]; exact h.zero_mem_nhd
    have hd := h.hasDerivAt_expChartFlow b X h0
    have hev : (fun t : ℝ => expChartFlow b X (0, t)) =ᶠ[𝓝 0]
        fun t : ℝ => t • (coordEquiv b).symm X := by
      have hc : Continuous (fun t : ℝ => t • (X : 𝔸)) := continuous_id.smul continuous_const
      have : ∀ᶠ t in 𝓝 (0 : ℝ), t • (X : 𝔸) ∈ h.nhd := by
        have h1 := hc.continuousAt (x := 0)
        rw [ContinuousAt, zero_smul] at h1
        exact h1 (h.isOpen_nhd.mem_nhds h.zero_mem_nhd)
      filter_upwards [this] with t ht
      simp only [expChartFlow, expChartProd, map_zero, ZeroMemClass.coe_zero, exp_zero, one_mul]
      rw [h.symm_exp ht, show t • (X : 𝔸) = ((t • X : 𝔤) : 𝔸) from rfl, subspaceProj_coe, map_smul]
    have hd2 : HasDerivAt (fun t : ℝ => t • (coordEquiv b).symm X) ((coordEquiv b).symm X) 0 := by
      simpa using (hasDerivAt_id (0 : ℝ)).smul_const ((coordEquiv b).symm X)
    exact hd.unique (hd2.congr_of_eventuallyEq hev)
  ·
    intro X f hf g x hx
    have hxN := hball x hx
    set u : EuclideanSpace ℝ (Fin d) → ℂ := fun y => f (g * h.expG (coordEquiv b y)) with hu
    have hud : Differentiable ℝ u := (h.contDiff_comp_coordEquiv hf g b).differentiable (by simp)
    have hφ := h.hasDerivAt_expChartFlow b X hxN
    have h1 : HasDerivAt (fun t : ℝ => u (expChartFlow b X (x, t)))
        (fderiv ℝ u x (expChartCoeff b X x)) 0 := by
      have := (hud (expChartFlow b X (x, 0))).hasFDerivAt.comp_hasDerivAt (x := (0 : ℝ)) hφ
      rw [h.expChartFlow_zero b X hxN] at this
      exact this
    have h2 := h.hasDerivAt_rightDeriv hf X (g * h.expG (coordEquiv b x))
    have hev : (fun t : ℝ => f (g * h.expG (coordEquiv b x) * h.expG (t • X))) =ᶠ[𝓝 0]
        fun t : ℝ => u (expChartFlow b X (x, t)) := by
      have hc : Continuous (fun t : ℝ => expChartProd b X (x, t)) :=
        (continuous_expChartProd b X).comp (continuous_const.prodMk continuous_id)
      have : ∀ᶠ t in 𝓝 (0 : ℝ), expChartProd b X (x, t) ∈ h.nhdOne :=
        hc.continuousAt.preimage_mem_nhds
          (h.isOpen_nhdOne.mem_nhds (h.expChartProd_zero_mem_nhdOne b X hxN))
      filter_upwards [this] with t ht
      simp only [hu]
      rw [h.expG_expChartFlow b X ht, mul_assoc]
    exact h2.unique (h1.congr_of_eventuallyEq hev)

end IsExpLieAlgebra

end GroundTheory.Automorphic
