import Mathlib
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.GroupDict
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsSheetCover
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.StatementsProved
import GroundTheory.HeightsAndTheta.Heights.CountingLowerBound.Assembly
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterSheet
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterBridgeG
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterBridgeL
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterGood
import Development.AutomorphicSpectrum.Proofs.MetricProofs.AnalyticOnNhdOfDifferentiableOn
import Development.AutomorphicSpectrum.Proofs.MetricProofs.MongeAmpereDensityChangeOfVariables
open NumberField Matrix MeasureTheory Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GroundTheory.Heights₂.Heights.FiniteCovolume
open scoped ENNReal InnerProductSpace

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Cusp
variable {K : Type} [Fintype K] {J : K → Type} [∀ k, Fintype (J k)] {n : ℕ}

theorem sheet_of_torus (Ψ : (((k : K) → J k) → ℂ) →ₗ[ℂ] (Fin (n + 1) → ℂ)) {z z' : (Σ k, J k) → ℂ}
    {y : Fin n → ℂ} (c : K → ℂ) (hz : z = GroundTheory.Heights₂.Heights.LowerBoundFree.torusSmul c z')
    (hΨ : Ψ (segre z) = Fin.cons 1 y) :
    Ψ (segre z') 0 ≠ 0 ∧ (fun i : Fin n => Ψ (segre z') i.succ / Ψ (segre z') 0) = y ∧
      sheetNorm Ψ z' = segre z := by
  have hs : segre z = (∏ k, c k) • segre z' := by
    rw [hz]
    exact segre_smul c z'
  have hcomp : ∀ j, (∏ k, c k) * Ψ (segre z') j = (Fin.cons (1 : ℂ) y : Fin (n + 1) → ℂ) j := by
    intro j
    rw [← hΨ, hs, map_smul, Pi.smul_apply, smul_eq_mul]
  have h0 : (∏ k, c k) * Ψ (segre z') 0 = 1 := by simpa using hcomp 0
  have hs0 : Ψ (segre z') 0 ≠ 0 := right_ne_zero_of_mul_eq_one h0
  refine ⟨hs0, ?_, ?_⟩
  · funext i
    have hi : (∏ k, c k) * Ψ (segre z') i.succ = y i := by simpa using hcomp i.succ
    rw [div_eq_iff hs0, ← hi]
    linear_combination (-(Ψ (segre z') i.succ)) * h0
  · show (Ψ (segre z') 0)⁻¹ • segre z' = segre z
    rw [hs, eq_inv_of_mul_eq_one_left h0]

theorem torus_log_re : ∀ (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (n : ℕ) (A : HermLine J) (z₁ z₂ : (Fin n → ℂ) → (Σ k, J k) → ℂ) (c : K → (Fin n → ℂ) → ℂ) (y : Fin n → ℂ), AnalyticAt ℂ z₁ y → (∀ k, ∃ i, z₁ y ⟨k, i⟩ ≠ 0) → (∀ k, AnalyticAt ℂ (c k) y) → (∀ k, c k y ≠ 0) → (∀ᶠ y' in 𝓝 y, z₂ y' = GroundTheory.Heights₂.Heights.LowerBoundFree.torusSmul (fun k => c k y') (z₁ y')) → ∃ g : (Fin n → ℂ) → ℂ, AnalyticAt ℂ g y ∧ ∀ᶠ y' in 𝓝 y, Real.log (A.h (z₂ y')) = Real.log (A.h (z₁ y')) + (g y').re := by
  intro K _ J _ n A z₁ z₂ c y hz hy hca hc0 hrel
  classical
  choose i0 hi0 using hy
  have hcont : ∀ᶠ y' in 𝓝 y, ∀ k, z₁ y' ⟨k, i0 k⟩ ≠ 0 :=
    eventually_all.mpr fun k => (analyticAt_coord hz ⟨k, i0 k⟩).continuousAt.eventually_ne (hi0 k)
  have hcne : ∀ᶠ y' in 𝓝 y, ∀ k, c k y' ≠ 0 :=
    eventually_all.mpr fun k => (hca k).continuousAt.eventually_ne (hc0 k)
  set G : (Fin n → ℂ) → ℂ := fun y' => ∑ k, ((A.a k : ℝ) : ℂ) * Complex.log (c k y' / c k y) with hG
  set C : ℝ := ∑ k, (A.a k : ℝ) * Real.log ‖c k y‖ with hC
  have hGan : AnalyticAt ℂ G y := by
    refine Finset.analyticAt_fun_sum _ fun k _ => analyticAt_const.mul ?_
    refine ((hca k).div analyticAt_const (hc0 k)).clog ?_
    show c k y / c k y ∈ Complex.slitPlane
    rw [div_self (hc0 k)]
    exact Complex.one_mem_slitPlane
  refine ⟨fun y' => G y' + (C : ℂ), hGan.add analyticAt_const, ?_⟩
  filter_upwards [hrel, hcont, hcne] with y' hr hγ0 hc
  have hpos : 0 < A.h (z₁ y') := A.pos _ fun k => ⟨i0 k, hγ0 k⟩
  have hsm : A.h (z₂ y') = (∏ k, ‖c k y'‖ ^ A.a k) * A.h (z₁ y') := by
    rw [hr]
    exact A.smul _ _ hc
  have hne : ∀ k, ‖c k y'‖ ^ A.a k ≠ 0 := fun k => zpow_ne_zero _ (norm_ne_zero_iff.mpr (hc k))
  have hterm : ∀ k, (((A.a k : ℝ) : ℂ) * Complex.log (c k y' / c k y)).re =
      (A.a k : ℝ) * Real.log ‖c k y'‖ - (A.a k : ℝ) * Real.log ‖c k y‖ := by
    intro k
    rw [Complex.re_ofReal_mul, Complex.log_re, norm_div,
      Real.log_div (norm_ne_zero_iff.mpr (hc k)) (norm_ne_zero_iff.mpr (hc0 k)), mul_sub]
  rw [hsm, Real.log_mul (Finset.prod_ne_zero_iff.mpr fun k _ => hne k) hpos.ne',
    Real.log_prod (fun k _ => hne k), Complex.add_re, Complex.ofReal_re]
  simp only [hG, hC, Complex.re_sum, Real.log_zpow, hterm, Finset.sum_sub_distrib]
  ring

theorem ram_sheet_null : ∀ (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (P : Ideal (MRing J)) (n : ℕ) (Ψ : (((k : K) → J k) → ℂ) →ₗ[ℂ] (Fin (n + 1) → ℂ)) (V : Set (Fin n → ℂ)) (γ : (Fin n → ℂ) → (Σ k, J k) → ℂ), IsArithVar P (n + 1) → IsGoodProj P Ψ → IsOpen V → DifferentiableOn ℂ γ V → (∀ t ∈ V, γ t ∈ mcPts P) → (∀ t ∈ V, ∀ t' ∈ V, γ t ∈ torusSat {γ t'} → t = t') → volume {t | t ∈ V ∧ Ψ (segre (γ t)) 0 ≠ 0 ∧ LinearMap.det (fderiv ℂ (sheetProj Ψ γ) t : (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ)) = 0} = 0 := by
  intro K _ J _ P n Ψ V γ hP hΨ hV hol hmem hinj
  have hγ := analyticOnNhd_of_differentiableOn hV hol
  apply ReciprocityTheory.AnForm.volume_eq_zero_of_locally_in_analytic_zero_set
  rintro u0 ⟨hu0, h00, -⟩
  have hc0 := (analyticAt_pi_iff.mp (analyticAt_psi_segre Ψ (hγ u0 hu0)) 0).continuousAt
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff_ball.mp
    (Filter.Eventually.and (hV.mem_nhds hu0 : ∀ᶠ u in 𝓝 u0, u ∈ V) (hc0.eventually_ne h00))
  refine ⟨Metric.ball u0 r, Metric.isOpen_ball, Metric.mem_ball_self hr,
    (convex_ball u0 r).isPreconnected, fun u => LinearMap.det (fderiv ℂ (sheetProj Ψ γ) u :
      (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ)), fun u hu => analyticAt_det_fderiv
        (analyticAt_sheetProj Ψ (hγ u (hball u hu).1) (hball u hu).2), ?_, ?_⟩
  · by_contra hall
    push Not at hall
    exact sheet_not_flat hP hΨ hV hγ hmem hinj Metric.isOpen_ball (fun u hu => (hball u hu).1)
      ⟨u0, Metric.mem_ball_self hr⟩ (fun u hu => (hball u hu).2) hall
  · rintro w ⟨⟨-, -, hd⟩, -⟩
    exact hd

theorem vanishing_sheet_measure_zero : ∀ (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (P : Ideal (MRing J)) (n : ℕ) (Ψ : (((k : K) → J k) → ℂ) →ₗ[ℂ] (Fin (n + 1) → ℂ)) (V : Set (Fin n → ℂ)) (γ : (Fin n → ℂ) → (Σ k, J k) → ℂ), IsArithVar P (n + 1) → IsGoodProj P Ψ → IsOpen V → DifferentiableOn ℂ γ V → (∀ t ∈ V, γ t ∈ mcPts P) → (∀ t ∈ V, ∀ t' ∈ V, γ t ∈ torusSat {γ t'} → t = t') → volume {t | t ∈ V ∧ Ψ (segre (γ t)) 0 = 0} = 0 := by
  intro K _ J _ P n Ψ V γ hP hΨ hV hol hmem hinj
  classical
  have hγ := analyticOnNhd_of_differentiableOn hV hol
  apply ReciprocityTheory.AnForm.volume_eq_zero_of_locally_in_analytic_zero_set
  rintro u0 ⟨hu0, -⟩
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hV u0 hu0
  refine ⟨Metric.ball u0 r, Metric.isOpen_ball, Metric.mem_ball_self hr,
    (convex_ball u0 r).isPreconnected, fun u => Ψ (segre (γ u)) 0,
    fun u hu => analyticAt_pi_iff.mp (analyticAt_psi_segre Ψ (hγ u (hball hu))) 0, ?_, ?_⟩
  · by_contra hall
    push Not at hall
    obtain ⟨i0, hi0⟩ : ∃ i0, Ψ (segre (γ u0)) i0 ≠ 0 := by
      by_contra h
      push Not at h
      exact hΨ _ (hmem u0 hu0) (funext h)
    have hi0ne : i0 ≠ 0 := by
      rintro rfl
      exact hi0 (hall u0 (Metric.mem_ball_self hr))
    set m : Fin n := i0.pred hi0ne
    have hm : m.succ = i0 := Fin.succ_pred i0 hi0ne
    set Ψ' : (((k : K) → J k) → ℂ) →ₗ[ℂ] (Fin (n + 1) → ℂ) :=
      (LinearMap.funLeft ℂ ℂ (Equiv.swap (0 : Fin (n + 1)) i0)).comp Ψ with hΨ'def
    have hΨ'app : ∀ w i, Ψ' w i = Ψ w (Equiv.swap 0 i0 i) := fun w i => rfl
    have hΨ' : IsGoodProj P Ψ' := by
      intro z hz h
      refine hΨ z hz (funext fun i => ?_)
      have := congrFun h (Equiv.swap 0 i0 i)
      rw [hΨ'app, Equiv.swap_apply_self] at this
      exact this
    have hg'c : ContinuousOn (fun u => Ψ' (segre (γ u)) 0) (Metric.ball u0 r) := fun u hu =>
      (analyticAt_pi_iff.mp (analyticAt_psi_segre Ψ' (hγ u (hball hu))) 0).continuousAt.continuousWithinAt
    set O := Metric.ball u0 r ∩ (fun u => Ψ' (segre (γ u)) 0) ⁻¹' {0}ᶜ with hOdef
    have hO : IsOpen O := hg'c.isOpen_inter_preimage Metric.isOpen_ball isOpen_compl_singleton
    have hu0O : u0 ∈ O := by
      refine ⟨Metric.mem_ball_self hr, ?_⟩
      show Ψ' (segre (γ u0)) 0 ≠ 0
      rw [hΨ'app, Equiv.swap_apply_left]
      exact hi0
    have h0O : ∀ u ∈ O, Ψ' (segre (γ u)) 0 ≠ 0 := fun u hu => hu.2
    have hanO : AnalyticOnNhd ℂ (sheetProj Ψ' γ) O := fun u hu =>
      analyticAt_sheetProj Ψ' (hγ u (hball hu.1)) (h0O u hu)
    have hzero : ∀ u ∈ O, sheetProj Ψ' γ u m = 0 := by
      intro u hu
      simp only [sheetProj]
      rw [hm, hΨ'app, Equiv.swap_apply_right, hall u hu.1, zero_div]
    have hdetO : ∀ u ∈ O, LinearMap.det (fderiv ℂ (sheetProj Ψ' γ) u :
        (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ)) = 0 := by
      intro u hu
      have hcoord : (fun v => sheetProj Ψ' γ v m) =ᶠ[𝓝 u] fun _ => 0 := by
        filter_upwards [hO.mem_nhds hu] with v hv
        exact hzero v hv
      have hd : HasFDerivAt (fun v => sheetProj Ψ' γ v m)
          ((ContinuousLinearMap.proj m).comp (fderiv ℂ (sheetProj Ψ' γ) u)) u :=
        (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin n => ℂ) m).hasFDerivAt.comp u
          (hanO u hu).differentiableAt.hasFDerivAt
      have hd0 : HasFDerivAt (fun v => sheetProj Ψ' γ v m) (0 : (Fin n → ℂ) →L[ℂ] ℂ) u :=
        (hasFDerivAt_const (0 : ℂ) u).congr_of_eventuallyEq hcoord
      have hrow := hd.unique hd0
      refine det_eq_zero_of_coord m fun v => ?_
      have := congrArg (fun T : (Fin n → ℂ) →L[ℂ] ℂ => T v) hrow
      simpa using this
    exact sheet_not_flat hP hΨ' hV hγ hmem hinj hO (fun u hu => hball hu.1) ⟨u0, hu0O⟩ h0O hdetO
  · rintro w ⟨⟨-, hw0⟩, -⟩
    exact hw0

theorem fibre_sheet_cover : ∀ (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (P : Ideal (MRing J)) (n nc : ℕ) (Bd : Set ((Σ k, J k) → ℂ)) (χ : Fin nc → GroundTheory.Heights₂.Heights.LowerBoundFree.SncChart P n Bd) (V B : ℕ → Set (Fin n → ℂ)) (γ : ℕ → (Fin n → ℂ) → (Σ k, J k) → ℂ) (Ψ : (((k : K) → J k) → ℂ) →ₗ[ℂ] (Fin (n + 1) → ℂ)), IsArithVar P (n + 1) → IsGoodProj P Ψ → (∀ z ∈ mcPts P, ∃ a, ∃ t : Fin n → ℂ, ‖t‖ ≤ 1 / 2 ∧ z ∈ torusSat {(χ a).γ t}) → IsSheetCover χ V B γ → (∀ m, volume (V m \ sheetReg Ψ (γ m) (V m)) = 0) → ∀ᵐ y : Fin n → ℂ, ∀ w ∈ fibre P Ψ y, ∃ m, ∃ t ∈ B m, t ∈ sheetReg Ψ (γ m) (V m) ∧ sheetProj Ψ (γ m) t = y ∧ sheetNorm Ψ (γ m t) = w := by
  intro K _ J _ P n nc Bd χ V B γ Ψ hP hΨ hcov hS hnull
  classical
  have hγ : ∀ m, AnalyticOnNhd ℂ (γ m) (V m) := fun m =>
    analyticOnNhd_of_differentiableOn (hS.isOpen m) (hS.hol m)
  set N : Fin nc → Set (Fin n → ℂ) := fun a =>
    {t ∈ Metric.ball (0 : Fin n → ℂ) 1 | (χ a).γ t ∉ torusSat (⋃ m, γ m '' B m)} with hN
  set Z₁ : Fin nc → Set (Fin n → ℂ) := fun a =>
    sheetProj Ψ (χ a).γ '' (N a ∩ {t | Ψ (segre ((χ a).γ t)) 0 ≠ 0}) with hZ₁
  set Z₂ : ℕ → Set (Fin n → ℂ) := fun m =>
    sheetProj Ψ (γ m) '' ((V m \ sheetReg Ψ (γ m) (V m)) ∩ {t | Ψ (segre (γ m t)) 0 ≠ 0}) with hZ₂
  have h1 : ∀ a, volume (Z₁ a) = 0 := fun a => by
    refine addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero volume (fun t ht => ?_)
      (measure_mono_null Set.inter_subset_left (hS.cover a))
    exact ((analyticAt_sheetProj Ψ ((χ a).analytic t ht.1.1) ht.2).differentiableAt.restrictScalars
      ℝ).differentiableWithinAt
  have h2 : ∀ m, volume (Z₂ m) = 0 := fun m => by
    refine addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero volume (fun t ht => ?_)
      (measure_mono_null Set.inter_subset_left (hnull m))
    exact ((analyticAt_sheetProj Ψ (hγ m t ht.1.1) ht.2).differentiableAt.restrictScalars
      ℝ).differentiableWithinAt
  have hae : ∀ᵐ y : Fin n → ℂ, y ∉ (⋃ a, Z₁ a) ∪ ⋃ m, Z₂ m :=
    measure_eq_zero_iff_ae_notMem.mp
      (measure_union_null (measure_iUnion_null h1) (measure_iUnion_null h2))
  filter_upwards [hae] with y hy w hw
  obtain ⟨z, hz, hzw, hΨw⟩ := hw
  obtain ⟨a, t, htn, _, rfl, c, hc, hzc⟩ := hcov z hz
  have hΨz : Ψ (segre z) = Fin.cons 1 y := by rw [hzw]; exact hΨw
  obtain ⟨hc0, hcy, -⟩ := sheet_of_torus Ψ c hzc hΨz
  have hcy' : sheetProj Ψ (χ a).γ t = y := hcy
  have htb : t ∈ Metric.ball (0 : Fin n → ℂ) 1 := by
    rw [mem_ball_zero_iff]
    linarith
  have htN : (χ a).γ t ∈ torusSat (⋃ m, γ m '' B m) := by
    by_contra hcon
    exact hy (Or.inl (Set.mem_iUnion.mpr ⟨a, t, ⟨⟨htb, hcon⟩, hc0⟩, hcy'⟩))
  obtain ⟨w', hw', c', hc', hwc⟩ := htN
  obtain ⟨m, t', ht', rfl⟩ := Set.mem_iUnion.mp hw'
  have hzc' : z = GroundTheory.Heights₂.Heights.LowerBoundFree.torusSmul (fun k => c k * c' k) (γ m t') := by
    rw [hzc, hwc]
    funext p
    simp [GroundTheory.Heights₂.Heights.LowerBoundFree.torusSmul, mul_assoc]
  obtain ⟨hm0, hmy, hmw⟩ := sheet_of_torus Ψ _ hzc' hΨz
  have hmy' : sheetProj Ψ (γ m) t' = y := hmy
  have htV := (hS.meas m).2 ht'
  refine ⟨m, t', ht', ?_, hmy', hmw.trans hzw⟩
  by_contra hcon
  exact hy (Or.inr (Set.mem_iUnion.mpr ⟨m, t', ⟨⟨htV, hcon⟩, hm0⟩, hmy'⟩))

theorem sheet_local : ∀ (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (P : Ideal (MRing J)) (n : ℕ) (Ψ : (((k : K) → J k) → ℂ) →ₗ[ℂ] (Fin (n + 1) → ℂ)) (V : Set (Fin n → ℂ)) (γ : (Fin n → ℂ) → (Σ k, J k) → ℂ) (t : Fin n → ℂ), IsArithVar P (n + 1) → IsOpen V → DifferentiableOn ℂ γ V → (∀ t ∈ V, γ t ∈ mcPts P) → t ∈ sheetReg Ψ γ V → ∃ (τ : (Fin n → ℂ) → Fin n → ℂ) (σ : (Fin n → ℂ) → (Σ k, J k) → ℂ) (c : K → (Fin n → ℂ) → ℂ), AnalyticAt ℂ τ (sheetProj Ψ γ t) ∧ τ (sheetProj Ψ γ t) = t ∧ ‖LinearMap.det ((fderiv ℂ τ (sheetProj Ψ γ t) : (Fin n → ℂ) →L[ℂ] (Fin n → ℂ)) : (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ))‖ ^ 2 * jacN (sheetProj Ψ γ) t = 1 ∧ AnalyticAt ℂ (fun y => γ (τ y)) (sheetProj Ψ γ t) ∧ IsSheet P Ψ (sheetProj Ψ γ t) (sheetNorm Ψ (γ t)) σ ∧ (∀ k, AnalyticAt ℂ (c k) (sheetProj Ψ γ t)) ∧ (∀ k, c k (sheetProj Ψ γ t) ≠ 0) ∧ ∀ᶠ y' in 𝓝 (sheetProj Ψ γ t), σ y' = GroundTheory.Heights₂.Heights.LowerBoundFree.torusSmul (fun k => c k y') (γ (τ y')) := by
  intro K _ J _ P n Ψ V γ t hP hV hol hmem ht
  classical
  have hγ := analyticOnNhd_of_differentiableOn hV hol
  have hQa := analyticAt_sheetProj Ψ (hγ t ht.1) ht.2.1
  have hd := ht.2.2
  set Ce := (fderiv ℂ (sheetProj Ψ γ) t).toContinuousLinearEquivOfDetNeZero hd with hCedef
  have hCe : (Ce : (Fin n → ℂ) →L[ℂ] (Fin n → ℂ)) = fderiv ℂ (sheetProj Ψ γ) t :=
    ContinuousLinearMap.coe_toContinuousLinearEquivOfDetNeZero _ hd
  have hstrict : HasStrictFDerivAt (sheetProj Ψ γ) (Ce : (Fin n → ℂ) →L[ℂ] (Fin n → ℂ)) t := by
    rw [hCe]
    exact hQa.hasStrictFDerivAt
  set F := hstrict.toOpenPartialHomeomorph (sheetProj Ψ γ) with hFdef
  have hFc : (F : (Fin n → ℂ) → (Fin n → ℂ)) = sheetProj Ψ γ := hstrict.toOpenPartialHomeomorph_coe
  have hus : t ∈ F.source := hstrict.mem_toOpenPartialHomeomorph_source
  have hyF : F t = sheetProj Ψ γ t := by rw [hFc]
  have hτa : AnalyticAt ℂ F.symm (sheetProj Ψ γ t) := by
    have := F.analyticAt_symm' (i := Ce) hus (by rw [hFc]; exact hQa) (by rw [hFc, hCe])
    rwa [hyF] at this
  have hτt : F.symm (sheetProj Ψ γ t) = t := by
    rw [← hyF]
    exact F.left_inv hus
  have hyt : sheetProj Ψ γ t ∈ F.target := hyF ▸ F.map_source hus
  have hright : ∀ᶠ y' in 𝓝 (sheetProj Ψ γ t), sheetProj Ψ γ (F.symm y') = y' := by
    filter_upwards [F.open_target.mem_nhds hyt] with y' hy'
    have := F.right_inv hy'
    rwa [hFc] at this
  have hder : HasFDerivAt F.symm (Ce.symm : (Fin n → ℂ) →L[ℂ] (Fin n → ℂ)) (sheetProj Ψ γ t) :=
    F.hasFDerivAt_symm hyt (by rw [hτt, hFc]; exact hstrict.hasFDerivAt)
  have hdet1 : LinearMap.det ((Ce.symm : (Fin n → ℂ) →L[ℂ] (Fin n → ℂ)) : (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ)) *
      LinearMap.det (fderiv ℂ (sheetProj Ψ γ) t : (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ)) = 1 := by
    rw [← hCe, ← LinearMap.det_comp]
    have hid : ((Ce.symm : (Fin n → ℂ) →L[ℂ] (Fin n → ℂ)) : (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ)) ∘ₗ
        ((Ce : (Fin n → ℂ) →L[ℂ] (Fin n → ℂ)) : (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ)) = LinearMap.id := by
      apply LinearMap.ext
      intro v
      simp
    rw [hid, LinearMap.det_id]
  have hγτ : AnalyticAt ℂ (fun y' => γ (F.symm y')) (sheetProj Ψ γ t) :=
    (hγ t ht.1 |>.comp_of_eq hτa hτt)
  set ψ : (Fin n → ℂ) → ℂ := fun y' => Ψ (segre (γ (F.symm y'))) 0 with hψdef
  have hψa : AnalyticAt ℂ ψ (sheetProj Ψ γ t) := analyticAt_pi_iff.mp (analyticAt_psi_segre Ψ hγτ) 0
  have hψ0 : ψ (sheetProj Ψ γ t) ≠ 0 := by
    simp only [hψdef, hτt]
    exact ht.2.1
  obtain ⟨k0⟩ := hP.1
  set c : K → (Fin n → ℂ) → ℂ := fun k y' => if k = k0 then (ψ y')⁻¹ else 1 with hcdef
  have hca : ∀ k, AnalyticAt ℂ (c k) (sheetProj Ψ γ t) := fun k => by
    by_cases hk : k = k0
    · simp only [hcdef, hk, if_true]
      exact hψa.inv hψ0
    · simp only [hcdef, hk, if_false]
      exact analyticAt_const
  have hcne : ∀ k y', ψ y' ≠ 0 → c k y' ≠ 0 := fun k y' h => by
    by_cases hk : k = k0
    · simp [hcdef, hk, h]
    · simp [hcdef, hk]
  have hprod : ∀ y', ∏ k, c k y' = (ψ y')⁻¹ := fun y' => by
    simp [hcdef, Finset.prod_ite_eq']
  set σ : (Fin n → ℂ) → (Σ k, J k) → ℂ := fun y' =>
    GroundTheory.Heights₂.Heights.LowerBoundFree.torusSmul (fun k => c k y') (γ (F.symm y')) with hσdef
  have hσa : AnalyticAt ℂ σ (sheetProj Ψ γ t) :=
    analyticAt_pi_iff.mpr fun p => (hca p.1).mul (analyticAt_coord hγτ p)
  have hseg : ∀ y', segre (σ y') = (ψ y')⁻¹ • segre (γ (F.symm y')) := fun y' => by
    rw [← hprod y']
    exact segre_smul (fun k => c k y') _
  refine ⟨F.symm, σ, c, hτa, hτt, ?_, hγτ, ⟨?_, ?_⟩, hca, fun k => hcne k _ hψ0,
    Filter.Eventually.of_forall fun _ => rfl⟩
  · rw [hder.fderiv]
    unfold jacN
    rw [← mul_pow, ← norm_mul, hdet1]
    simp
  · rw [hseg]
    simp only [hψdef, hτt]
    rfl
  · filter_upwards [hσa.eventually_analyticAt,
      hτa.continuousAt.eventually (by rw [hτt]; exact hV.mem_nhds ht.1),
      hψa.continuousAt.eventually_ne hψ0, hright] with y' h1 h2 h3 h4
    refine ⟨h1.differentiableAt, mcPts_smul hP.2.1.2.1 (fun k => c k y') (fun k => hcne k y' h3)
      (hmem _ h2), ?_⟩
    rw [hseg, map_smul]
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp only [Pi.smul_apply, smul_eq_mul, Fin.cons_zero]
      exact inv_mul_cancel₀ h3
    · have := congrFun h4 j
      simp only [sheetProj] at this
      simp only [Pi.smul_apply, smul_eq_mul, Fin.cons_succ]
      rw [← this, div_eq_inv_mul]

theorem reg_null : ∀ (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (P : Ideal (MRing J)) (n : ℕ) (Ψ : (((k : K) → J k) → ℂ) →ₗ[ℂ] (Fin (n + 1) → ℂ)) (V : Set (Fin n → ℂ)) (γ : (Fin n → ℂ) → (Σ k, J k) → ℂ), IsArithVar P (n + 1) → IsGoodProj P Ψ → IsOpen V → DifferentiableOn ℂ γ V → (∀ t ∈ V, γ t ∈ mcPts P) → (∀ t ∈ V, ∀ t' ∈ V, γ t ∈ torusSat {γ t'} → t = t') → volume (V \ sheetReg Ψ γ V) = 0 := by
  intro K _ J _ P n Ψ V γ hP hΨ hV hol hmem hinj
  refine measure_mono_null ?_ (measure_union_null (vanishing_sheet_measure_zero K J P n Ψ V γ hP hΨ hV hol hmem hinj)
    (ram_sheet_null K J P n Ψ V γ hP hΨ hV hol hmem hinj))
  rintro t ⟨htV, ht⟩
  by_cases h0 : Ψ (segre (γ t)) 0 = 0
  · exact Or.inl ⟨htV, h0⟩
  · refine Or.inr ⟨htV, h0, ?_⟩
    by_contra hd
    exact ht ⟨htV, h0, hd⟩

theorem sheet_term : ∀ (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (P : Ideal (MRing J)) (n : ℕ) (Ψ : (((k : K) → J k) → ℂ) →ₗ[ℂ] (Fin (n + 1) → ℂ)) (V : Set (Fin n → ℂ)) (γ : (Fin n → ℂ) → (Σ k, J k) → ℂ) (A : HermLine J) (G : ((Σ k, J k) → ℂ) → ℝ) (t : Fin n → ℂ), IsArithVar P (n + 1) → IsOpen V → DifferentiableOn ℂ γ V → (∀ t ∈ V, γ t ∈ mcPts P) → t ∈ sheetReg Ψ γ V → ContDiffAt ℝ 2 (fun t' => Real.log (A.h (γ t'))) t → (∀ w' ∈ torusSat {γ t}, G w' = G (γ t)) → sheetProj Ψ γ t ∉ badSet P Ψ → sheetDensity P Ψ (fun (_ : Fin n) z => Real.log (A.h z)) G (sheetProj Ψ γ t) (sheetNorm Ψ (γ t)) = G (γ t) * maDensity (fun (_ : Fin n) t' => Real.log (A.h (γ t'))) t / jacN (sheetProj Ψ γ) t := by
  intro K _ J _ P n Ψ V γ A G t hP hV hol hmem ht hC hG hbad
  classical
  obtain ⟨τ, σ, c, hτa, hτt, hdet, hγτ, hσS, hca, hc0, hσc⟩ := sheet_local K J P n Ψ V γ t hP hV hol hmem ht
  have hex : ∃ g, IsSheet P Ψ (sheetProj Ψ γ t) (sheetNorm Ψ (γ t)) g := ⟨σ, hσS⟩
  unfold sheetDensity
  rw [dif_pos hex]
  obtain ⟨g, hgdef⟩ : ∃ g, g = hex.choose := ⟨_, rfl⟩
  have hg : IsSheet P Ψ (sheetProj Ψ γ t) (sheetNorm Ψ (γ t)) g := hgdef ▸ hex.choose_spec
  rw [← hgdef]
  have hseg : (fun y' => segre (σ y')) =ᶠ[𝓝 (sheetProj Ψ γ t)] fun y' => segre (g y') := by
    by_contra hne
    exact hbad ⟨_, σ, g, hσS, hg, hne⟩
  have hga : AnalyticAt ℂ g (sheetProj Ψ γ t) := sheet_analyticAt osgood hg
  have hσa : AnalyticAt ℂ σ (sheetProj Ψ γ t) := sheet_analyticAt osgood hσS
  have hσ0 := hσS.2.self_of_nhds.2.1.1
  choose i0 hi0 using hσ0
  have hcont : ∀ᶠ y' in 𝓝 (sheetProj Ψ γ t), ∀ k, σ y' ⟨k, i0 k⟩ ≠ 0 :=
    eventually_all.mpr fun k => (analyticAt_coord hσa ⟨k, i0 k⟩).continuousAt.eventually_ne (hi0 k)
  have hrel : ∀ᶠ y' in 𝓝 (sheetProj Ψ γ t), g y' = GroundTheory.Heights₂.Heights.LowerBoundFree.torusSmul
      (fun k => g y' ⟨k, i0 k⟩ / σ y' ⟨k, i0 k⟩) (σ y') := by
    filter_upwards [hcont, hseg] with y' h1 h2
    exact (eq_bsmul_of_segre_eq i0 h1 h2).2
  have hg0 : ∀ k, g (sheetProj Ψ γ t) ⟨k, i0 k⟩ ≠ 0 :=
    (eq_bsmul_of_segre_eq i0 hcont.self_of_nhds hseg.self_of_nhds).1
  obtain ⟨G₁, hG₁a, hG₁⟩ := torus_log_re K J n A σ g (fun k y' => g y' ⟨k, i0 k⟩ / σ y' ⟨k, i0 k⟩) _ hσa
    (fun k => ⟨i0 k, hi0 k⟩) (fun k => (analyticAt_coord hga _).div (analyticAt_coord hσa _) (hi0 k))
    (fun k => div_ne_zero (hg0 k) (hi0 k)) hrel
  have hz : ∀ k, ∃ i, γ (τ (sheetProj Ψ γ t)) ⟨k, i⟩ ≠ 0 := by
    rw [hτt]
    exact (hmem t ht.1).1
  obtain ⟨G₂, hG₂a, hG₂⟩ := torus_log_re K J n A (fun y => γ (τ y)) σ c _ hγτ hz hca hc0 hσc
  have hCτ : ContDiffAt ℝ 2 (fun t' => Real.log (A.h (γ t'))) (τ (sheetProj Ψ γ t)) := by
    rw [hτt]
    exact hC
  have hMA := maDensity_const_eq_normSq_jacobian_mul n (fun t' => Real.log (A.h (γ t')))
    (fun y' => Real.log (A.h (g y'))) τ (fun y' => G₁ y' + G₂ y') (sheetProj Ψ γ t) hτa (hG₁a.add hG₂a) hCτ
    (by
      filter_upwards [hG₁, hG₂] with y' h1 h2
      rw [h1, h2, Complex.add_re]
      ring)
  rw [hMA, hτt]
  have hgt : g (sheetProj Ψ γ t) ∈ torusSat {γ t} := by
    have h1 : segre (g (sheetProj Ψ γ t)) = (Ψ (segre (γ t)) 0)⁻¹ • segre (γ t) := hg.1
    obtain ⟨a, ha, haz⟩ := sameOrbit_of_segre (hmem t ht.1).1 _ (inv_ne_zero ht.2.1) h1
    exact ⟨γ t, rfl, a, ha, haz⟩
  rw [hG _ hgt]
  have hJ : jacN (sheetProj Ψ γ) t ≠ 0 := fun h0 => by
    rw [h0, mul_zero] at hdet
    exact zero_ne_one hdet
  field_simp
  linear_combination (G (γ t) * maDensity (fun (_ : Fin n) t' => Real.log (A.h (γ t'))) t) * hdet

theorem sheets_tsum_eq {α β : Type*} (F : Set β) (T : ℕ → Set α) (Φ : ℕ → α → β) (f : β → ℝ) (hF : F.Finite)
    (hmap : ∀ m, ∀ t ∈ T m, Φ m t ∈ F)
    (hinj : ∀ m, ∀ t ∈ T m, ∀ m', ∀ t' ∈ T m', Φ m t = Φ m' t' → m = m' ∧ t = t')
    (hsurj : ∀ w ∈ F, ∃ m, ∃ t ∈ T m, Φ m t = w) :
    ∑' m, ∑ᶠ t ∈ T m, f (Φ m t) = ∑ᶠ w ∈ F, f w := by
  have hE : Pairwise (Function.onFun Disjoint fun m => Φ m '' T m) := by
    intro m m' hne
    refine Set.disjoint_left.mpr ?_
    rintro _ ⟨t, ht, rfl⟩ ⟨t', ht', h⟩
    exact hne (hinj m t ht m' t' ht' h.symm).1
  have hU : ⋃ m, Φ m '' T m = F := by
    refine Set.Subset.antisymm (Set.iUnion_subset ?_) fun w hw => ?_
    · rintro m _ ⟨t, ht, rfl⟩
      exact hmap m t ht
    · obtain ⟨m, t, ht, rfl⟩ := hsurj w hw
      exact Set.mem_iUnion.mpr ⟨m, t, ht, rfl⟩
  have h := tsum_finsum_disjointed hE hU (G := F) (by simpa using hF) f
  have hsub : ∀ m, Φ m '' T m ∩ F = Φ m '' T m := fun m => Set.inter_eq_left.mpr (by
    rintro _ ⟨t, ht, rfl⟩
    exact hmap m t ht)
  simp only [hsub, Set.inter_self] at h
  rw [← h]
  refine tsum_congr fun m => ?_
  rw [finsum_mem_image]
  intro t ht t' ht' he
  exact (hinj m t ht m t' ht' he).2

theorem norm_fibSum_le {n : ℕ} {D : Set (Fin n → ℂ)} {Q : (Fin n → ℂ) → Fin n → ℂ} {h : (Fin n → ℂ) → ℝ}
    {y : Fin n → ℂ} (hfin : (D ∩ Q ⁻¹' {y}).Finite) :
    ‖fibSum D Q h y‖ ≤ fibSum D Q (fun u => |h u|) y := by
  simp only [fibSum]
  rw [finsum_mem_eq_finite_toFinset_sum _ hfin, finsum_mem_eq_finite_toFinset_sum _ hfin]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun u _ => ?_)
  rw [Real.norm_eq_abs, abs_div, abs_of_nonneg (show (0 : ℝ) ≤ jacN Q u from by unfold jacN; positivity)]

theorem area_tsum {n : ℕ} (O : ℕ → Set (Fin n → ℂ)) (Q : ℕ → (Fin n → ℂ) → Fin n → ℂ)
    (h : ℕ → (Fin n → ℂ) → ℝ) (hO : ∀ m, IsOpen (O m))
    (hQ : ∀ m, ∀ u ∈ O m, AnalyticAt ℂ (Q m) u ∧
      LinearMap.det (fderiv ℂ (Q m) u : (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ)) ≠ 0)
    (hh : ∀ m, IntegrableOn (h m) (O m)) (hfin : ∀ m y, (O m ∩ Q m ⁻¹' {y}).Finite)
    (hs : Summable fun m => ∫ u in O m, |h m u|) :
    ∫ y, ∑' m, fibSum (O m) (Q m) (h m) y = ∑' m, ∫ u in O m, h m u := by
  have hA := fun m => area_open (hO m) (hQ m) (hh m) (ae_of_all _ (hfin m))
  have hA' := fun m => area_open (hO m) (hQ m) (h := fun u => |h m u|) (hh m).abs (ae_of_all _ (hfin m))
  have hsn : Summable fun m => ∫ y, ‖fibSum (O m) (Q m) (h m) y‖ := by
    refine Summable.of_nonneg_of_le (fun m => integral_nonneg fun _ => norm_nonneg _) (fun m => ?_) hs
    rw [(hA' m).2]
    exact integral_mono (hA m).1.norm (hA' m).1 fun y => norm_fibSum_le (hfin m y)
  rw [← integral_tsum_of_summable_integral_norm (fun m => (hA m).1) hsn]
  exact tsum_congr fun m => ((hA m).2).symm

theorem finsum_inter_indicator {α : Type*} (F E : Set α) (f : α → ℝ) :
    ∑ᶠ x ∈ F ∩ E, f x = ∑ᶠ x ∈ F, E.indicator f x := by
  rw [finsum_mem_def, finsum_mem_def, Set.indicator_indicator]

theorem sheet_pair_eq {P : Ideal (MRing J)} {Bd : Set ((Σ k, J k) → ℂ)} {nc : ℕ}
    {χ : Fin nc → GroundTheory.Heights₂.Heights.LowerBoundFree.SncChart P n Bd} {V B : ℕ → Set (Fin n → ℂ)}
    {γ : ℕ → (Fin n → ℂ) → (Σ k, J k) → ℂ} (hS : IsSheetCover χ V B γ)
    (Ψ : (((k : K) → J k) → ℂ) →ₗ[ℂ] (Fin (n + 1) → ℂ)) {m m' : ℕ} {t t' : Fin n → ℂ}
    (ht : t ∈ B m) (ht' : t' ∈ B m') (h0 : Ψ (segre (γ m t)) 0 ≠ 0) (h0' : Ψ (segre (γ m' t')) 0 ≠ 0)
    (h : sheetNorm Ψ (γ m t) = sheetNorm Ψ (γ m' t')) : m = m' ∧ t = t' := by
  have htV := (hS.meas m).2 ht
  have htV' := (hS.meas m').2 ht'
  have hT := sheetNorm_eq_torusSat Ψ (hS.mem m' t' htV').1.1 h0 h0' h
  by_cases hm : m = m'
  · subst hm
    exact ⟨rfl, hS.inj m t htV t' htV' hT⟩
  · exfalso
    obtain ⟨_, rfl, c, hc, hw⟩ := hT
    exact hS.disj m m' hm t ht ⟨γ m' t', ⟨t', ht', rfl⟩, c, hc, hw⟩

theorem ptsIntegral_sheets : ∀ (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (P : Ideal (MRing J)) (n nc : ℕ) (Bd : Set ((Σ k, J k) → ℂ)) (χ : Fin nc → GroundTheory.Heights₂.Heights.LowerBoundFree.SncChart P n Bd) (V B : ℕ → Set (Fin n → ℂ)) (γ : ℕ → (Fin n → ℂ) → (Σ k, J k) → ℂ) (A : HermLine J) (G : ((Σ k, J k) → ℂ) → ℝ), IsArithVar P (n + 1) → (∀ z ∈ mcPts P, ∃ a, ∃ t : Fin n → ℂ, ‖t‖ ≤ 1 / 2 ∧ z ∈ torusSat {(χ a).γ t}) → IsSheetCover χ V B γ → (∀ m, ContDiffOn ℝ 2 (fun t => Real.log (A.h (γ m t))) (V m)) → (∀ w ∈ mcPts P \ Bd, ∀ w' ∈ torusSat {w}, G w' = G w) → (∀ m, IntegrableOn (fun t => G (γ m t) * maDensity (fun (_ : Fin n) t' => Real.log (A.h (γ m t'))) t) (B m)) → Summable (fun m => ∫ t in B m, |G (γ m t) * maDensity (fun (_ : Fin n) t' => Real.log (A.h (γ m t'))) t|) → ptsIntegral (e := n) P (fun _ z => Real.log (A.h z)) G = ∑' m, ∫ t in B m, G (γ m t) * maDensity (fun (_ : Fin n) t' => Real.log (A.h (γ m t'))) t := by
  intro K _ J _ P n nc Bd χ V B γ A G hP hcov hS hC hG hI hsum
  classical
  have hex : ∃ Ψ : (((k : K) → J k) → ℂ) →ₗ[ℂ] (Fin (n + 1) → ℂ), IsGoodProj P Ψ := goodProjExists K J P n hP
  obtain ⟨Ψ, hΨdef⟩ : ∃ Ψ, Ψ = hex.choose := ⟨_, rfl⟩
  have hΨ : IsGoodProj P Ψ := hΨdef ▸ hex.choose_spec
  have hval : ptsIntegral (e := n) P (fun _ z => Real.log (A.h z)) G =
      ptsIntegralAt P Ψ (fun _ z => Real.log (A.h z)) G := by
    unfold ptsIntegral
    rw [dif_pos hex, ← hΨdef]
  have hγ : ∀ m, AnalyticOnNhd ℂ (γ m) (V m) := fun m =>
    analyticOnNhd_of_differentiableOn (hS.isOpen m) (hS.hol m)
  have hmem : ∀ m, ∀ t ∈ V m, γ m t ∈ mcPts P := fun m t ht => (hS.mem m t ht).1
  set F : ℕ → (Fin n → ℂ) → ℝ := fun m t =>
    G (γ m t) * maDensity (fun (_ : Fin n) t' => Real.log (A.h (γ m t'))) t with hFdef
  set O : ℕ → Set (Fin n → ℂ) := fun m => sheetReg Ψ (γ m) (V m) with hOdef
  set Q : ℕ → (Fin n → ℂ) → Fin n → ℂ := fun m => sheetProj Ψ (γ m) with hQdef
  set h : ℕ → (Fin n → ℂ) → ℝ := fun m => (B m).indicator (F m) with hhdef
  have hOo : ∀ m, IsOpen (O m) := fun m => isOpen_sheetReg Ψ (hS.isOpen m) (hγ m)
  have hQ : ∀ m, ∀ u ∈ O m, AnalyticAt ℂ (Q m) u ∧
      LinearMap.det (fderiv ℂ (Q m) u : (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ)) ≠ 0 := fun m u hu =>
    ⟨analyticAt_sheetProj Ψ (hγ m u hu.1) hu.2.1, hu.2.2⟩
  have hnull : ∀ m, volume (V m \ O m) = 0 := fun m =>
    reg_null K J P n Ψ (V m) (γ m) hP hΨ (hS.isOpen m) (hS.hol m) (hmem m) (hS.inj m)
  have hBm : ∀ m, MeasurableSet (B m) := fun m => (hS.meas m).1
  have hint : ∀ m, IntegrableOn (h m) (O m) := fun m => ((hI m).integrable_indicator (hBm m)).integrableOn
  have hset : ∀ m, (O m ∩ B m : Set (Fin n → ℂ)) =ᵐ[volume] B m := fun m => by
    refine (ae_eq_set.mpr ⟨?_, ?_⟩)
    · rw [Set.diff_eq_empty.mpr Set.inter_subset_right]; exact measure_empty
    · exact measure_mono_null (show B m \ (O m ∩ B m) ⊆ V m \ O m from
        fun t ht => ⟨(hS.meas m).2 ht.1, fun hO => ht.2 ⟨hO, ht.1⟩⟩) (hnull m)
  have hIB : ∀ m, ∫ u in O m, h m u = ∫ t in B m, F m t := fun m => by
    rw [setIntegral_indicator (hBm m)]
    exact setIntegral_congr_set (hset m)
  have hIBabs : ∀ m, ∫ u in O m, |h m u| = ∫ t in B m, |F m t| := fun m => by
    have : (fun u => |h m u|) = (B m).indicator (fun t => |F m t|) := by
      funext u
      by_cases hu : u ∈ B m <;> simp [hhdef, hu]
    rw [this, setIntegral_indicator (hBm m)]
    exact setIntegral_congr_set (hset m)
  have hfin : ∀ m y, (O m ∩ Q m ⁻¹' {y}).Finite := fun m y =>
    (sheetProj_fibre_finite hP hΨ (hmem m) (hS.inj m) y).subset fun t ht => ⟨⟨ht.1.1, ht.1.2.1⟩, ht.2⟩
  have hs : Summable fun m => ∫ u in O m, |h m u| := by
    simp_rw [hIBabs]
    exact hsum
  have key := area_tsum O Q h hOo hQ hint hfin hs
  simp_rw [hIB] at key
  rw [hval, ← key]
  unfold ptsIntegralAt
  have hff := fibreFinite K J P n Ψ hP hΨ
  have hbad : ∀ᵐ y : Fin n → ℂ, y ∉ badSet P Ψ :=
    measure_eq_zero_iff_ae_notMem.mp (badSet_null osgood hff)
  refine integral_congr_ae ?_
  filter_upwards [fibre_sheet_cover K J P n nc Bd χ V B γ Ψ hP hΨ hcov hS hnull, hbad] with y hy hyb
  set f := sheetDensity P Ψ (fun (_ : Fin n) z => Real.log (A.h z)) G y with hfdef
  have hT := sheets_tsum_eq (fibre P Ψ y) (fun m => (O m ∩ Q m ⁻¹' {y}) ∩ B m)
    (fun m t => sheetNorm Ψ (γ m t)) f (hff y) ?_ ?_ ?_
  · rw [← hT]
    refine tsum_congr fun m => ?_
    simp only [fibSum]
    rw [finsum_inter_indicator]
    refine finsum_mem_congr rfl fun t ht => ?_
    by_cases htB : t ∈ B m
    · rw [Set.indicator_of_mem htB]
      have hy' : Q m t = y := ht.2
      have := sheet_term K J P n Ψ (V m) (γ m) A G t hP (hS.isOpen m) (hS.hol m) (hmem m) ht.1
        ((hC m).contDiffAt ((hS.isOpen m).mem_nhds ht.1.1)) (hG _ (hS.mem m t ht.1.1))
        (by rw [show sheetProj Ψ (γ m) t = y from hy']; exact hyb)
      rw [show sheetProj Ψ (γ m) t = y from hy'] at this
      rw [hfdef, this]
      show _ = (B m).indicator (F m) t / _
      rw [Set.indicator_of_mem htB]
    · simp [hhdef, htB]
  · rintro m t ⟨⟨htO, hty⟩, -⟩
    have := sheetNorm_mem_fibre hP.1 hP.2.1.2.1 Ψ (γ m) (hmem m t htO.1) htO.2.1
    rwa [show sheetProj Ψ (γ m) t = y from hty] at this
  · rintro m t ⟨⟨htO, -⟩, htB⟩ m' t' ⟨⟨htO', -⟩, htB'⟩ he
    exact sheet_pair_eq hS Ψ htB htB' htO.2.1 htO'.2.1 he
  · intro w hw
    obtain ⟨m, t, htB, htO, hty, hw'⟩ := hy w hw
    exact ⟨m, t, ⟨⟨htO, hty⟩, htB⟩, hw'⟩

end GlobalTheory.CompanionTheory.Ar.Cusp
