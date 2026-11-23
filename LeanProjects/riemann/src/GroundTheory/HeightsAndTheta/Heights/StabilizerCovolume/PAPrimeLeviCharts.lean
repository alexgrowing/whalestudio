import Mathlib
import GroundTheory.HeightsAndTheta.Heights.StabilizerCovolume.StAPrimeLeviCharts
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StProjHoloLocal
import ReciprocityTheory.AnalyticForms.PotentialTheory.PshShiftA
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.NineStatements

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology GroundTheory.Heights₂.Heights.LowerBoundFree
open ReciprocityTheory.AnForm (levi levi_congr levi_comp levi_add_smul levi_re_analytic continuousOn_levi)

namespace APrimeLeviCharts

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

omit [∀ k, Fintype (ι k)] in

theorem isOpen_blocks : IsOpen {z : (Σ k, ι k) → ℂ | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0} := by
  have h : {z : (Σ k, ι k) → ℂ | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0} = ⋂ k, ⋃ i, {z | z ⟨k, i⟩ ≠ 0} := by
    ext z; simp
  rw [h]
  exact isOpen_iInter_of_finite fun k => isOpen_iUnion fun i =>
    isOpen_ne_fun (continuous_apply _) continuous_const

theorem contDiffAt_log_h {A : HermLine ι} (hA : IsSmoothHerm A) {z : (Σ k, ι k) → ℂ}
    (hz : ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) : ContDiffAt ℝ 2 (fun y => Real.log (A.h y)) z := by
  have h1 : ContDiffAt ℝ 2 A.h z :=
    (hA.contDiffAt (isOpen_blocks.mem_nhds hz)).of_le (WithTop.coe_le_coe.mpr le_top)
  exact h1.log (A.pos z hz).ne'

theorem levi_log_h_torus {J : Type} [Fintype J] {A : HermLine ι} (hA : IsSmoothHerm A)
    {τ₁ τ₂ : (J → ℂ) → (Σ k, ι k) → ℂ} {u₀ : J → ℂ} (h₁ : AnalyticAt ℂ τ₁ u₀) (h₂ : AnalyticAt ℂ τ₂ u₀)
    (hrel : ∀ᶠ u in 𝓝 u₀, (∀ k, ∃ i, τ₂ u ⟨k, i⟩ ≠ 0) ∧
      ∃ c : K → ℂ, (∀ k, c k ≠ 0) ∧ τ₁ u = torusSmul c (τ₂ u))
    (e : J → ℂ) :
    levi ((fun y => Real.log (A.h y)) ∘ τ₁) u₀ e = levi ((fun y => Real.log (A.h y)) ∘ τ₂) u₀ e := by
  classical
  have hb := hrel.self_of_nhds.1
  choose i hi using hb

  set c : K → (J → ℂ) → ℂ := fun k u => τ₁ u ⟨k, i k⟩ / τ₂ u ⟨k, i k⟩ with hcdef
  have hcan : ∀ k, AnalyticAt ℂ (c k) u₀ := fun k =>
    ((analyticAt_pi_iff.1 h₁) ⟨k, i k⟩).div ((analyticAt_pi_iff.1 h₂) ⟨k, i k⟩) (hi k)
  have hne : ∀ᶠ u in 𝓝 u₀, ∀ k, τ₂ u ⟨k, i k⟩ ≠ 0 := by
    rw [eventually_all]
    intro k
    exact ((analyticAt_pi_iff.1 h₂) ⟨k, i k⟩).continuousAt.eventually_ne (hi k)
  have hrel' : ∀ᶠ u in 𝓝 u₀, (∀ k, ∃ i, τ₂ u ⟨k, i⟩ ≠ 0) ∧ (∀ k, c k u ≠ 0) ∧
      τ₁ u = torusSmul (fun k => c k u) (τ₂ u) := by
    filter_upwards [hrel, hne] with u hu hn
    obtain ⟨hbl, c', hc'0, hc'⟩ := hu
    have hcc : ∀ k, c k u = c' k := by
      intro k
      show τ₁ u ⟨k, i k⟩ / τ₂ u ⟨k, i k⟩ = c' k
      rw [hc']
      exact mul_div_cancel_right₀ _ (hn k)
    refine ⟨hbl, fun k => by rw [hcc]; exact hc'0 k, ?_⟩
    rw [hc']
    congr 1
    funext k
    exact (hcc k).symm
  have hc0 : ∀ k, c k u₀ ≠ 0 := hrel'.self_of_nhds.2.1

  set H : (J → ℂ) → ℂ := fun u =>
    ∑ k, ((A.a k : ℝ) : ℂ) * (Complex.log (c k u / c k u₀) + Complex.log (c k u₀)) with hHdef
  have hH : AnalyticAt ℂ H u₀ := by
    have hk : ∀ k ∈ Finset.univ, AnalyticAt ℂ
        (fun u => ((A.a k : ℝ) : ℂ) * (Complex.log (c k u / c k u₀) + Complex.log (c k u₀))) u₀ := by
      intro k _
      refine analyticAt_const.mul (AnalyticAt.add ?_ analyticAt_const)
      refine ((hcan k).div analyticAt_const (hc0 k)).clog ?_
      show c k u₀ / c k u₀ ∈ Complex.slitPlane
      rw [div_self (hc0 k)]
      exact Complex.one_mem_slitPlane
    have hs := Finset.analyticAt_sum _ hk
    convert hs using 1
    funext u
    simp only [hHdef, Finset.sum_apply]
  have hHre : ∀ u, (∀ k, c k u ≠ 0) → (H u).re = ∑ k, (A.a k : ℝ) * Real.log ‖c k u‖ := by
    intro u hu
    simp only [hHdef, Complex.re_sum, Complex.re_ofReal_mul, Complex.add_re, Complex.log_re, norm_div]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Real.log_div (norm_ne_zero_iff.2 (hu k)) (norm_ne_zero_iff.2 (hc0 k))]
    ring
  have heq : ((fun y => Real.log (A.h y)) ∘ τ₁) =ᶠ[𝓝 u₀]
      fun u => ((fun y => Real.log (A.h y)) ∘ τ₂) u + 1 * (H u).re := by
    filter_upwards [hrel'] with u hu
    obtain ⟨hbl, hcu, hτ⟩ := hu
    have hs := A.smul (fun k => c k u) (τ₂ u) hcu
    have hprod : ∀ k ∈ Finset.univ, ‖c k u‖ ^ A.a k ≠ 0 := fun k _ =>
      zpow_ne_zero _ (norm_ne_zero_iff.2 (hcu k))
    simp only [Function.comp_apply, one_mul]
    rw [hHre u hcu, hτ]
    show Real.log (A.h (fun p => c p.1 u * τ₂ u p)) = _
    rw [hs, Real.log_mul (Finset.prod_ne_zero_iff.2 hprod) (A.pos _ hbl).ne', Real.log_prod hprod]
    simp only [Real.log_zpow]
    ring
  have hf : ContDiffAt ℝ 2 ((fun y => Real.log (A.h y)) ∘ τ₂) u₀ :=
    (contDiffAt_log_h hA hrel'.self_of_nhds.1).comp u₀ h₂.restrictScalars.contDiffAt
  have hg : ContDiffAt ℝ 2 (fun u => (H u).re) u₀ :=
    Complex.reCLM.contDiff.contDiffAt.comp u₀ hH.restrictScalars.contDiffAt
  rw [levi_congr heq, levi_add_smul 1 hf hg, levi_re_analytic hH]
  ring

section Charts

variable {P : Ideal (MRing ι)} {d : ℕ}

theorem analyticAt_sec (M : CxModel P d) {e : OpenPartialHomeomorph M.Xc (Fin d → ℂ)}
    (he : ReciprocityTheory.AnForm.M.IsCompatChart M.atlas e) {U : Set M.Xc} (hU : IsOpen U)
    {s : M.Xc → (Σ k, ι k) → ℂ} (hs : ∀ p, M.atlas.HoloOn U fun y => s y p)
    {u : Fin d → ℂ} (hu : u ∈ e.target) (huU : e.symm u ∈ U) :
    AnalyticAt ℂ (fun u => s (e.symm u)) u := by
  obtain ⟨j, hj⟩ := M.atlas.cover (e.symm u)
  set V : Set (Fin d → ℂ) := e.target ∩ e.symm ⁻¹' (U ∩ (M.atlas.chart j).source) with hV
  have hVo : IsOpen V := e.continuousOn_symm.isOpen_inter_preimage e.open_target
    (hU.inter (M.atlas.chart j).open_source)
  have huV : u ∈ V := ⟨hu, huU, hj⟩
  refine analyticAt_pi_iff.2 fun p => ?_
  have h1 : AnalyticAt ℂ (M.atlas.chart j ∘ e.symm) u := (he j).2 u ⟨hu, hj⟩
  have h2 : AnalyticAt ℂ ((fun y' => s y' p) ∘ (M.atlas.chart j).symm) ((M.atlas.chart j ∘ e.symm) u) := by
    refine hs p j _ ⟨(M.atlas.chart j).map_source hj, ?_⟩
    show (M.atlas.chart j).symm ((M.atlas.chart j) (e.symm u)) ∈ U
    rw [(M.atlas.chart j).left_inv hj]
    exact huU
  refine (h2.comp h1).congr ?_
  filter_upwards [hVo.mem_nhds huV] with u' hu'
  simp only [Function.comp_apply]
  rw [(M.atlas.chart j).left_inv hu'.2.2]

end Charts

end APrimeLeviCharts

theorem APrimeLeviCharts.proof (hP : ProjHoloLocal.Statement) : APrimeLeviCharts.Statement := by
  intro II Ψ _ K _ ι _ Ω _ _ E _ _ D M C kc
  classical
  set ψ := C.chart kc with hψ
  have hcompat : ReciprocityTheory.AnForm.M.IsCompatChart M.atlas ψ := C.compat kc
  have hsm : IsSmoothHerm D.A' := D.A'_pos.1
  set φ : ((Σ k, ι k) → ℂ) → ℝ := fun y => Real.log (D.A'.h y) with hφ

  have hsec : ∀ x : M.Xc, ∃ s : M.Xc → (Σ k, ι k) → ℂ, ∃ U : Set M.Xc, IsOpen U ∧ x ∈ U ∧
      (∀ y ∈ U, s y ∈ mcPts (mCoordIdeal D.y) ∧ M.proj (s y) = y) ∧
        ∀ p, M.atlas.HoloOn U fun y => s y p := by
    intro x
    obtain ⟨U, hUo, hxU, s, hs, hsh⟩ := M.sections x
    exact ⟨s, U, hUo, hxU, hs, hsh⟩
  choose sec U hUo hxU hs hsh using hsec

  have hNo : ∀ x, IsOpen (ψ.target ∩ ψ.symm ⁻¹' U x) := fun x =>
    ψ.continuousOn_symm.isOpen_inter_preimage ψ.open_target (hUo x)

  have hgan : ∀ x, ∀ u ∈ ψ.target ∩ ψ.symm ⁻¹' U x, AnalyticAt ℂ (fun u => sec x (ψ.symm u)) u :=
    fun x u hu => APrimeLeviCharts.analyticAt_sec M hcompat (hUo x) (hsh x) hu.1 hu.2
  have hgC : ∀ x, ∀ u ∈ ψ.target ∩ ψ.symm ⁻¹' U x, ContDiffAt ℝ 2 (φ ∘ fun u => sec x (ψ.symm u)) u :=
    fun x u hu => (APrimeLeviCharts.contDiffAt_log_h hsm (hs x _ hu.2).1.1).comp u
      (hgan x u hu).restrictScalars.contDiffAt

  have hind : ∀ x₁ x₂, ∀ y ∈ ψ.target, ψ.symm y ∈ U x₁ → ψ.symm y ∈ U x₂ → ∀ v,
      levi (φ ∘ fun u => sec x₁ (ψ.symm u)) y v = levi (φ ∘ fun u => sec x₂ (ψ.symm u)) y v := by
    intro x₁ x₂ y hy h₁ h₂ v
    have hO : IsOpen (ψ.target ∩ ψ.symm ⁻¹' (U x₁ ∩ U x₂)) :=
      ψ.continuousOn_symm.isOpen_inter_preimage ψ.open_target ((hUo x₁).inter (hUo x₂))
    refine APrimeLeviCharts.levi_log_h_torus hsm (hgan x₁ y ⟨hy, h₁⟩) (hgan x₂ y ⟨hy, h₂⟩) ?_ v
    filter_upwards [hO.mem_nhds ⟨hy, h₁, h₂⟩] with u hu
    have e₁ := hs x₁ _ hu.2.1
    have e₂ := hs x₂ _ hu.2.2
    exact ⟨e₂.1.1, (M.fibre _ e₂.1 _ e₁.1).1 (by rw [e₁.2, e₂.2])⟩
  refine ⟨fun y v => levi (φ ∘ fun u => sec (ψ.symm y) (ψ.symm u)) y v, ?_, ?_⟩
  ·
    intro p hp
    set x₀ := ψ.symm p.1 with hx₀
    have hp₀ : p.1 ∈ ψ.target ∩ ψ.symm ⁻¹' U x₀ := ⟨hp.1, hxU x₀⟩
    have hC : ContinuousOn (fun q : (Fin D.n → ℂ) × (Fin D.n → ℂ) =>
        levi (φ ∘ fun u => sec x₀ (ψ.symm u)) q.1 q.2) ((ψ.target ∩ ψ.symm ⁻¹' U x₀) ×ˢ Set.univ) :=
      continuousOn_levi (hNo x₀) fun u hu => (hgC x₀ u hu).contDiffWithinAt
    have hnhds : (ψ.target ∩ ψ.symm ⁻¹' U x₀) ×ˢ (Set.univ : Set (Fin D.n → ℂ)) ∈ 𝓝 p :=
      prod_mem_nhds ((hNo x₀).mem_nhds hp₀) Filter.univ_mem
    refine ((hC.continuousAt hnhds).congr ?_).continuousWithinAt
    filter_upwards [hnhds] with q hq
    exact (hind _ _ q.1 hq.1.1 (hxU _) hq.1.2 q.2).symm
  ·
    intro z hz hzs w v hv
    obtain ⟨γ, hγ0, hγw, hγev, hγv⟩ := hv
    obtain ⟨W, hWo, hzW, F, hFd, hF⟩ := hP II Ψ K ι Ω E D M ψ hcompat z hz hzs
    set y₀ := ψ (M.proj z) with hy₀
    set x := ψ.symm y₀ with hx
    have hxz : x = M.proj z := ψ.left_inv hzs
    have hy₀N : y₀ ∈ ψ.target ∩ ψ.symm ⁻¹' U x := ⟨ψ.map_source hzs, hxU x⟩

    have hWγ : ∀ᶠ t in 𝓝 (0 : ℂ), γ t ∈ W :=
      hγw.continuousAt.preimage_mem_nhds (by rw [hγ0]; exact hWo.mem_nhds hzW)
    obtain ⟨S, hS, hSp⟩ := (hγev.and hWγ).exists_mem
    have hγan : AnalyticAt ℂ γ 0 :=
      DifferentiableOn.analyticAt (fun t ht => (hSp t ht).1.1.differentiableWithinAt) hS
    set β : ℂ → Fin D.n → ℂ := fun t => F (γ t) with hβ
    have hβan : AnalyticAt ℂ β 0 :=
      DifferentiableOn.analyticAt (fun t ht =>
        ((hFd.differentiableAt (hWo.mem_nhds (hSp t ht).2)).comp t (hSp t ht).1.1).differentiableWithinAt) hS
    have hβψ : ∀ t ∈ S, M.proj (γ t) ∈ ψ.source ∧ ψ (M.proj (γ t)) = β t := fun t ht =>
      hF (γ t) ⟨(hSp t ht).2, (hSp t ht).1.2⟩
    have hβ0 : β 0 = y₀ := by
      rw [← (hβψ 0 (mem_of_mem_nhds hS)).2, hγ0]
    have hβv : HasDerivAt β v 0 := by
      refine hγv.congr_of_eventuallyEq ?_
      filter_upwards [hS] with t ht
      exact (hβψ t ht).2.symm

    have hβN : ∀ᶠ t in 𝓝 (0 : ℂ), β t ∈ ψ.target ∩ ψ.symm ⁻¹' U x :=
      hβan.continuousAt.preimage_mem_nhds (by rw [hβ0]; exact (hNo x).mem_nhds hy₀N)
    have hrelC : ∀ᶠ t in 𝓝 (0 : ℂ), (∀ k, ∃ i, sec x (ψ.symm (β t)) ⟨k, i⟩ ≠ 0) ∧
        ∃ c : K → ℂ, (∀ k, c k ≠ 0) ∧ γ t = torusSmul c (sec x (ψ.symm (β t))) := by
      filter_upwards [hS, hβN] with t ht htN
      have e₁ := hs x _ htN.2
      have hpr : M.proj (γ t) = ψ.symm (β t) := by
        rw [← (hβψ t ht).2, ψ.left_inv (hβψ t ht).1]
      exact ⟨e₁.1.1, (M.fibre _ e₁.1 _ (hSp t ht).1.2).1 (by rw [e₁.2, hpr])⟩

    set L₁ : (Fin 1 → ℂ) →L[ℂ] ℂ := ContinuousLinearMap.proj 0 with hL₁
    have hL0 : L₁ 0 = 0 := map_zero L₁
    have hLt : Tendsto L₁ (𝓝 0) (𝓝 0) := by
      have h := L₁.continuous.tendsto 0
      rwa [hL0] at h
    set e₁ : Fin 1 → ℂ := fun _ => 1 with he₁
    have hLe : L₁ e₁ = 1 := rfl
    have hτ₁ : AnalyticAt ℂ (γ ∘ L₁) 0 := hγan.comp_of_eq (L₁.analyticAt 0) hL0
    have hβL : AnalyticAt ℂ (β ∘ L₁) 0 := hβan.comp_of_eq (L₁.analyticAt 0) hL0
    have hβL0 : (β ∘ L₁) 0 = y₀ := by simp [hL0, hβ0]
    have hτ₂ : AnalyticAt ℂ ((fun u => sec x (ψ.symm u)) ∘ (β ∘ L₁)) 0 :=
      (hgan x y₀ hy₀N).comp_of_eq hβL hβL0

    have hγD : HasFDerivAt (γ ∘ L₁) ((ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ) w).comp L₁) 0 := by
      have h := hγw.hasFDerivAt
      rw [← hL0] at h
      exact h.comp 0 L₁.hasFDerivAt
    have s1 := levi_comp (φ := φ) e₁ hτ₁
      (by simp only [Function.comp_apply, hL0, hγ0]; exact APrimeLeviCharts.contDiffAt_log_h hsm hz.1)
    rw [hγD.fderiv] at s1
    simp only [Function.comp_apply, hL0, hγ0, ContinuousLinearMap.coe_comp', ContinuousLinearMap.smulRight_apply,
      ContinuousLinearMap.one_apply, hLe, one_smul] at s1

    have hβD : HasFDerivAt (β ∘ L₁) ((ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ) v).comp L₁) 0 := by
      have h := hβv.hasFDerivAt
      rw [← hL0] at h
      exact h.comp 0 L₁.hasFDerivAt
    have s3 := levi_comp (φ := φ ∘ fun u => sec x (ψ.symm u)) e₁ hβL (by rw [hβL0]; exact hgC x y₀ hy₀N)
    rw [hβD.fderiv, hβL0] at s3
    simp only [ContinuousLinearMap.coe_comp', Function.comp_apply, ContinuousLinearMap.smulRight_apply,
      ContinuousLinearMap.one_apply, hLe, one_smul] at s3

    have s2 := APrimeLeviCharts.levi_log_h_torus hsm hτ₁ hτ₂ (hLt.eventually hrelC) e₁
    rw [← s1]
    exact s2.trans s3

end GroundTheory.Heights₂.Heights.NineStatements
