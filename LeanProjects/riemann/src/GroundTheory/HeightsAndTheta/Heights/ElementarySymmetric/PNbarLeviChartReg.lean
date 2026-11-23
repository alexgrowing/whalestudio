import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.StRefChartDisc
import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.StConeTangentDisc
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PNbarSmooth
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PVertFactorSmooth
import GroundTheory.HeightsAndTheta.Heights.Intersections.RegularizedCurvature
import ReciprocityTheory.AnalyticForms.PotentialTheory.HessCEqZeroOfEventuallyEqZero
import ReciprocityTheory.AnalyticForms.PotentialTheory.PshShiftA
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.NineStatements

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo GroundTheory.Heights₂.Heights.LowerBoundFree Filter Topology
open ReciprocityTheory.AnForm (levi levi_comp levi_add_smul levi_re_analytic levi_congr)

namespace NbarLeviChartReg

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {II : IntersectionSystem} {Ψ : Type} [Fintype Ψ] {Ω : Type} [Field Ω] [Algebra ℚ Ω]
  {E : Ψ → Type} [∀ τ, AddCommGroup (E τ)] [∀ τ, Module Ω (E τ)]

theorem analyticAt_disc {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] {f : ℂ → F}
    (hf : AnalyticAt ℂ f 0) : AnalyticAt ℂ (fun u : Fin 1 → ℂ => f (u 0)) 0 :=
  hf.comp_of_eq ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin 1 => ℂ) 0).analyticAt 0) rfl

theorem fderiv_disc {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] {f : ℂ → F} {d : F}
    (hf : HasDerivAt f d 0) : fderiv ℂ (fun u : Fin 1 → ℂ => f (u 0)) 0 (fun _ => 1) = d := by
  have hL : HasFDerivAt (fun u : Fin 1 → ℂ => u 0)
      (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin 1 => ℂ) 0) 0 :=
    (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin 1 => ℂ) 0).hasFDerivAt
  have h : HasFDerivAt (fun u : Fin 1 → ℂ => f (u 0))
      ((ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ) d).comp
        (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin 1 => ℂ) 0)) 0 :=
    hf.hasFDerivAt.comp (0 : Fin 1 → ℂ) hL
  rw [h.fderiv]
  simp

theorem levi_const_mul {J : Type} [Fintype J] {f : (J → ℂ) → ℝ} {z : J → ℂ} (c : ℝ)
    (hf : ContDiffAt ℝ 2 f z) (w : J → ℂ) : levi (fun y => c * f y) z w = c * levi f z w := by
  have h := levi_add_smul (f := fun _ => (0 : ℝ)) c contDiffAt_const hf w
  simp only [zero_add] at h
  rw [h, Inter.RegularizedCurvature.levi_const, zero_add]

theorem vertFactor_local (D : ComponentData II Ψ K ι Ω E) {p : ℕ} (hp : p ∈ D.S) {z : (Σ k, ι k) → ℂ}
    (hz : z ∈ mcPts (mCoordIdeal D.y)) :
    ∃ T : ((Σ k, ι k) → ℂ) → ℂ, AnalyticAt ℂ T z ∧ T z ≠ 0 ∧
      ∀ᶠ y in 𝓝 z, y ∈ mcPts (mCoordIdeal D.y) → D.vertFactor p y = ‖T y‖ := by
  obtain ⟨dG, dH, G, H, hG, hH, hdeg, hrel, hHz⟩ := VertFactorSmooth.exists_forms D hp hz
  have hpos := VertFactorPos.proof II Ψ K ι Ω E D p hp z hz
  rw [VertFactorSmooth.vertFactor_eq D hp hz hG hH hdeg hrel hHz] at hpos
  have hHa := Inter.RegularizedCurvature.analyticAt_eval_map H z
  refine ⟨fun y => eval y (map (Int.castRingHom ℂ) G) / eval y (map (Int.castRingHom ℂ) H),
    (Inter.RegularizedCurvature.analyticAt_eval_map G z).div hHa hHz, norm_pos_iff.mp hpos, ?_⟩
  filter_upwards [hHa.continuousAt.eventually_ne hHz] with y hy hyP
  exact VertFactorSmooth.vertFactor_eq D hp hyP hG hH hdeg hrel hy

open MuRegSmooth TopNPoly NbarSmooth in

theorem regNbarQ_smooth_eq [DecidableEq Ψ] (hE : HermExtend.Statement) (hP : ProjSmoothAlong.Statement)
    (D : ComponentData II Ψ K ι Ω E) (H : HodgeData D) (M : XModel D) (S : LogLogRegularisationSetting M D.Xo (muLine H))
    (B p q : ℕ) (t : ℝ) (hsm : M.atlas.Smooth (S.regWeight t)) :
    IsSmoothHerm (regNbarQ H M S B p q t) ∧ ∀ z ∈ mcPts (mCoordIdeal D.y),
      (regNbarQ H M S B p q t).h z = (S.ref.h z * Real.exp (S.regWeight t (M.proj z))) ^ q *
        (∏ p' ∈ D.SB B, D.vertFactor p' z) ^ q * D.A'.h z ^ p := by
  have hVS := VertFactorSmooth.proof VertFactorPos.proof
  set P := mCoordIdeal D.y with hPdef
  set a : K → ℤ := (q : ℤ) • muTwDeg H B + (p : ℤ) • D.a' with ha
  set F : ((Σ k, ι k) → ℂ) → ℝ := fun z => (S.ref.h z * Real.exp (S.regWeight t (M.proj z))) ^ q *
    (∏ p' ∈ D.SB B, D.vertFactor p' z) ^ q * D.A'.h z ^ p with hFdef
  have hSB : ∀ p' ∈ D.SB B, p' ∈ D.S := fun p' hp' => (Finset.mem_filter.1 hp').1
  have hMH : IsMultiHomogIdeal P := D.arith.2.1.2.1
  have hpos : ∀ z ∈ mcPts P, 0 < F z := by
    intro z hz
    have h2 : 0 < ∏ p' ∈ D.SB B, D.vertFactor p' z := Finset.prod_pos fun p' hp' =>
      VertFactorPos.proof II Ψ K ι Ω E D p' (hSB p' hp') z hz
    exact mul_pos (mul_pos (pow_pos (mul_pos (S.ref.pos z hz.1) (Real.exp_pos _)) q) (pow_pos h2 q))
      (pow_pos (D.A'.pos z hz.1) p)
  have hhom : ∀ z ∈ mcPts P, ∀ c : K → ℂ, (∀ k, c k ≠ 0) →
      F (torusSmul c z) = (∏ k, ‖c k‖ ^ a k) * F z := by
    intro z hz c hc
    have hcz : torusSmul c z ∈ mcPts P := mcPts_smul hMH c hc hz
    have hproj : M.proj (torusSmul c z) = M.proj z := ((M.fibre z hz _ hcz).2 ⟨c, hc, rfl⟩).symm
    have href : S.ref.h (torusSmul c z) = (∏ k, ‖c k‖ ^ H.aMu k) * S.ref.h z := by
      have := S.ref.smul c z hc
      rw [S.ref_deg] at this
      exact this
    have hA : D.A'.h (torusSmul c z) = (∏ k, ‖c k‖ ^ D.a' k) * D.A'.h z := by
      have := D.A'.smul c z hc
      rw [D.A'_deg] at this
      exact this
    have hV : ∀ p' ∈ D.SB B, D.vertFactor p' (torusSmul c z) =
        (∏ k, ‖c k‖ ^ D.vdeg p' k) * D.vertFactor p' z :=
      fun p' hp' => (hVS II Ψ K ι Ω E D p' (hSB p' hp')).1 z hz c hc
    have hk : ∀ k, ‖c k‖ ^ a k = (‖c k‖ ^ (muTwDeg H B) k) ^ q * (‖c k‖ ^ D.a' k) ^ p := by
      intro k
      have hx : ‖c k‖ ≠ 0 := norm_ne_zero_iff.mpr (hc k)
      have hak : a k = (q : ℤ) * (muTwDeg H B) k + (p : ℤ) * D.a' k := by
        simp only [ha, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      rw [hak, zpow_add₀ hx, zpow_mul', zpow_natCast, zpow_mul', zpow_natCast]
    have hprod : (∏ k, ‖c k‖ ^ a k) = ((∏ k, ‖c k‖ ^ H.aMu k) *
        ∏ p' ∈ D.SB B, ∏ k, ‖c k‖ ^ D.vdeg p' k) ^ q * (∏ k, ‖c k‖ ^ D.a' k) ^ p := by
      rw [Finset.prod_congr rfl fun k _ => hk k, Finset.prod_mul_distrib, Finset.prod_pow, Finset.prod_pow,
        muTwDeg, prod_norm_zpow_add_sum hc]
    simp only [hFdef]
    rw [hproj, href, hA, Finset.prod_congr rfl hV, Finset.prod_mul_distrib, hprod]
    ring
  have hsmooth : SmoothAlong (mcPts P) F :=
    smoothAlong_mul (smoothAlong_mul
      (smoothAlong_pow (smoothAlong_mul (smoothAlong_of_contDiffOn S.ref_smooth)
        (smoothAlong_exp (hP II Ψ K ι Ω E D M _ hsm))) q)
      (smoothAlong_pow (smoothAlong_prod _ fun p' hp' => (hVS II Ψ K ι Ω E D p' (hSB p' hp')).2) q))
      (smoothAlong_pow (smoothAlong_of_contDiffOn D.A'_pos.1) p)
  obtain ⟨Z, hZa, hZs, hZh⟩ := hE K ι P a F hMH hpos hhom hsmooth
  have hon : ∀ z ∈ mcPts P, (hermOfFun ι a F).h z = F z := fun z hz =>
    hermOfFun_h_of_mem hMH hhom hz (hpos z hz)
  refine ⟨?_, fun z hz => (smoothRep_h _ hz).trans (hon z hz)⟩
  show IsSmoothHerm (smoothRep P (hermOfFun ι a F))
  exact smoothRep_smooth_of (Z := Z) hZa hZs fun z hz => (hZh z hz).trans (hon z hz).symm

end NbarLeviChartReg

open NbarLeviChartReg in

theorem NbarLeviChartReg.proof (hDisc : ConeTangentDisc.Statement) (hProj : ProjChartHolo.Statement)
    (hRef : RefChartDisc.Statement) (hE : HermExtend.Statement) (hP : ProjSmoothAlong.Statement) :
    NbarLeviChartReg.Statement := by
  intro II Ψ _ _ K _ ι _ Ω _ _ E _ _ D H M S _ B p q t hsm z hz w hw k hk
  obtain ⟨γ, hγ0, hγd, hγa, hγm⟩ := hDisc II Ψ K ι Ω E D z hz w hw
  subst hγ0
  have hsrc : M.proj (γ 0) ∈ (S.R.chart k).source := S.R.mid_subset_source k hk
  have hχ := hProj II Ψ K ι Ω E D M (S.R.chart k) (S.R.compat k) γ hγa hγm hsrc
  obtain ⟨G, hGa, hGe⟩ := hRef II Ψ K ι Ω E D H M S k γ hγa hγm hsrc
  refine ⟨deriv (fun s => S.R.chart k (M.proj (γ s))) 0,
    ⟨γ, rfl, hγd, ?_, hχ.differentiableAt.hasDerivAt⟩, ?_⟩
  · filter_upwards [hγa.eventually_analyticAt, hγm] with s hs1 hs2
    exact ⟨hs1.differentiableAt, hs2⟩
  obtain ⟨hNs, hNe⟩ := regNbarQ_smooth_eq hE hP D H M S B p q t hsm
  have hSB : ∀ p' ∈ D.SB B, p' ∈ D.S := fun p' hp' => (Finset.mem_filter.1 hp').1
  have hex : ∀ p' ∈ D.SB B, ∃ T : ((Σ k, ι k) → ℂ) → ℂ, AnalyticAt ℂ T (γ 0) ∧ T (γ 0) ≠ 0 ∧
      ∀ᶠ y in 𝓝 (γ 0), y ∈ mcPts (mCoordIdeal D.y) → D.vertFactor p' y = ‖T y‖ :=
    fun p' hp' => vertFactor_local D (hSB p' hp') hz
  choose! T hTa hT0 hTe using hex
  have hTta : AnalyticAt ℂ (fun y => ∏ p' ∈ D.SB B, T p' y) (γ 0) := (D.SB B).analyticAt_fun_prod hTa
  have hTt0 : (∏ p' ∈ D.SB B, T p' (γ 0)) ≠ 0 := Finset.prod_ne_zero_iff.2 hT0
  have hΓa : AnalyticAt ℂ (fun u : Fin 1 → ℂ => γ (u 0)) 0 := analyticAt_disc hγa
  have hΓd : fderiv ℂ (fun u : Fin 1 → ℂ => γ (u 0)) 0 (fun _ => 1) = w := fderiv_disc hγd
  have hχ1 : AnalyticAt ℂ (fun u : Fin 1 → ℂ => S.R.chart k (M.proj (γ (u 0)))) 0 := analyticAt_disc hχ
  have hχd : fderiv ℂ (fun u : Fin 1 → ℂ => S.R.chart k (M.proj (γ (u 0)))) 0 (fun _ => 1) =
      deriv (fun s => S.R.chart k (M.proj (γ s))) 0 := fderiv_disc hχ.differentiableAt.hasDerivAt
  have hG1 : AnalyticAt ℂ (fun u : Fin 1 → ℂ => G (u 0)) 0 := analyticAt_disc hGa
  have hO : {y : (Σ k, ι k) → ℂ | ∀ k, ∃ i, y ⟨k, i⟩ ≠ 0} ∈ 𝓝 (γ 0) := MuRegSmooth.isOpen_blocks.mem_nhds hz.1
  have hlogN : ContDiffAt ℝ 2 (fun y => Real.log ((regNbarQ H M S B p q t).h y)) (γ 0) :=
    ((hNs.contDiffAt hO).of_le (WithTop.coe_le_coe.2 le_top)).log ((regNbarQ H M S B p q t).pos _ hz.1).ne'
  have hlogA : ContDiffAt ℝ 2 (fun y => Real.log (D.A'.h y)) (γ 0) :=
    ((D.A'_pos.1.contDiffAt hO).of_le (WithTop.coe_le_coe.2 le_top)).log (D.A'.pos _ hz.1).ne'
  have hx0 : S.R.chart k (M.proj (γ 0)) ∈ (S.R.chart k).target := (S.R.chart k).map_source hsrc
  have hcf : ContDiffAt ℝ 2 (S.R.chartFun (S.regWeight t) k) (S.R.chart k (M.proj (γ 0))) := by
    have hq : ContDiffAt ℝ 2 (S.R.q k) (S.R.chart k (M.proj (γ 0))) :=
      ((S.R.q_smooth k).contDiffAt ((S.R.chart k).open_target.mem_nhds hx0)).of_le (WithTop.coe_le_coe.2 le_top)
    have hφ : ContDiffAt ℝ 2 (S.regWeight t ∘ (S.R.chart k).symm) (S.R.chart k (M.proj (γ 0))) :=
      ((ReciprocityTheory.AnForm.M.PLAux.contDiffOn_compat (S.R.compat k) isOpen_univ hsm).contDiffAt
        (by simpa using (S.R.chart k).open_target.mem_nhds hx0)).of_le (WithTop.coe_le_coe.2 le_top)
    exact hq.add hφ

  have hγz : Tendsto γ (𝓝 0) (𝓝 (γ 0)) := hγa.continuousAt.tendsto
  have hcont : Tendsto (fun s => M.proj (γ s)) (𝓝 0) (𝓝 (M.proj (γ 0))) :=
    (M.cont (γ 0) hz).tendsto.comp (tendsto_nhdsWithin_iff.2 ⟨hγz, hγm⟩)
  have hsrcE : ∀ᶠ s in 𝓝 (0 : ℂ), M.proj (γ s) ∈ (S.R.chart k).source :=
    hcont ((S.R.chart k).open_source.mem_nhds hsrc)
  have hTE : ∀ᶠ s in 𝓝 (0 : ℂ), ∀ p' ∈ D.SB B, γ s ∈ mcPts (mCoordIdeal D.y) →
      D.vertFactor p' (γ s) = ‖T p' (γ s)‖ :=
    hγz.eventually ((Filter.eventually_all_finset _).2 hTe)
  have hE0 : ∀ᶠ s in 𝓝 (0 : ℂ), Real.log ((regNbarQ H M S B p q t).h (γ s)) =
      (q : ℝ) * (S.R.chartFun (S.regWeight t) k (S.R.chart k (M.proj (γ s))) + (-1) * (G s).re) +
        (q : ℝ) * Real.log ‖∏ p' ∈ D.SB B, T p' (γ s)‖ + (p : ℝ) * Real.log (D.A'.h (γ s)) := by
    filter_upwards [hγm, hGe, hsrcE, hTE] with s hsm' hsG hss hsT
    have hvf : ∏ p' ∈ D.SB B, D.vertFactor p' (γ s) = ‖∏ p' ∈ D.SB B, T p' (γ s)‖ := by
      rw [norm_prod]
      exact Finset.prod_congr rfl fun p' hp' => hsT p' hp' hsm'
    have hv0 : 0 < ∏ p' ∈ D.SB B, D.vertFactor p' (γ s) := Finset.prod_pos fun p' hp' =>
      VertFactorPos.proof II Ψ K ι Ω E D p' (hSB p' hp') _ hsm'
    have href := S.ref.pos _ hsm'.1
    have hA := D.A'.pos _ hsm'.1
    have hX : (S.ref.h (γ s) * Real.exp (S.regWeight t (M.proj (γ s)))) ^ q ≠ 0 :=
      (pow_pos (mul_pos href (Real.exp_pos _)) q).ne'
    have hY : (∏ p' ∈ D.SB B, D.vertFactor p' (γ s)) ^ q ≠ 0 := (pow_pos hv0 q).ne'
    have hZ : D.A'.h (γ s) ^ p ≠ 0 := (pow_pos hA p).ne'
    rw [hNe _ hsm', Real.log_mul (mul_ne_zero hX hY) hZ, Real.log_mul hX hY, Real.log_pow, Real.log_pow,
      Real.log_pow, Real.log_mul href.ne' (Real.exp_pos _).ne', Real.log_exp, hvf, hsG]
    simp only [Regular.PotentialCharts.chartFun, (S.R.chart k).left_inv hss]
    ring

  set A1 : (Fin 1 → ℂ) → ℝ := fun u => S.R.chartFun (S.regWeight t) k (S.R.chart k (M.proj (γ (u 0))))
    with hA1def
  set R1 : (Fin 1 → ℂ) → ℝ := fun u => (G (u 0)).re with hR1def
  set L2 : (Fin 1 → ℂ) → ℝ := fun u => Real.log ‖∏ p' ∈ D.SB B, T p' (γ (u 0))‖ with hL2def
  set L3 : (Fin 1 → ℂ) → ℝ := fun u => Real.log (D.A'.h (γ (u 0))) with hL3def
  have hEv : (fun y => Real.log ((regNbarQ H M S B p q t).h y)) ∘ (fun u : Fin 1 → ℂ => γ (u 0)) =ᶠ[𝓝 0]
      fun u => (q : ℝ) * (A1 u + (-1) * R1 u) + (q : ℝ) * L2 u + (p : ℝ) * L3 u := by
    have ht : Tendsto (fun u : Fin 1 → ℂ => u 0) (𝓝 0) (𝓝 0) := by
      simpa using (continuous_apply (0 : Fin 1)).tendsto (0 : Fin 1 → ℂ)
    exact ht.eventually hE0
  have hlevL : levi (fun y => Real.log ((regNbarQ H M S B p q t).h y)) (γ 0) w =
      levi ((fun y => Real.log ((regNbarQ H M S B p q t).h y)) ∘ (fun u : Fin 1 → ℂ => γ (u 0))) 0
        (fun _ => 1) := by
    have h := levi_comp (fun _ => (1 : ℂ)) hΓa hlogN
    rw [hΓd] at h
    exact h.symm
  have hA1c : ContDiffAt ℝ 2 A1 0 := hcf.comp (0 : Fin 1 → ℂ) (hχ1.restrictScalars.contDiffAt (n := 2))
  have hA1l : levi A1 0 (fun _ => 1) = levi (S.R.chartFun (S.regWeight t) k) (S.R.chart k (M.proj (γ 0)))
      (deriv (fun s => S.R.chart k (M.proj (γ s))) 0) := by
    have h := levi_comp (φ := S.R.chartFun (S.regWeight t) k) (fun _ => (1 : ℂ)) hχ1 hcf
    rw [hχd] at h
    exact h
  have hR1c : ContDiffAt ℝ 2 R1 0 := by
    have h := (Complex.reCLM.contDiff (n := 2)).contDiffAt.comp (0 : Fin 1 → ℂ)
      (hG1.restrictScalars.contDiffAt (n := 2))
    convert h using 1
    funext u
    simp [hR1def]
  have hR1l : levi R1 0 (fun _ => 1) = 0 := levi_re_analytic hG1 _
  have hL2 := Inter.RegularizedCurvature.log_norm_pluriharmonic (T := fun u : Fin 1 → ℂ => ∏ p' ∈ D.SB B, T p' (γ (u 0)))
    (hTta.comp_of_eq hΓa rfl) hTt0 (fun _ => 1)
  have hL2c : ContDiffAt ℝ 2 L2 0 := hL2.1
  have hL2l : levi L2 0 (fun _ => 1) = 0 := hL2.2
  have hL3c : ContDiffAt ℝ 2 L3 0 := hlogA.comp (0 : Fin 1 → ℂ) (hΓa.restrictScalars.contDiffAt (n := 2))
  have hL3l : levi L3 0 (fun _ => 1) = levi (fun y => Real.log (D.A'.h y)) (γ 0) w := by
    have h := levi_comp (fun _ => (1 : ℂ)) hΓa hlogA
    rw [hΓd] at h
    exact h
  have hf1 : ContDiffAt ℝ 2 (fun u => A1 u + (-1) * R1 u) 0 := hA1c.add (contDiffAt_const.mul hR1c)
  have hq1 : ContDiffAt ℝ 2 (fun u => (q : ℝ) * (A1 u + (-1) * R1 u)) 0 := contDiffAt_const.mul hf1
  have hq12 : ContDiffAt ℝ 2 (fun u => (q : ℝ) * (A1 u + (-1) * R1 u) + (q : ℝ) * L2 u) 0 :=
    hq1.add (contDiffAt_const.mul hL2c)
  rw [hlevL, levi_congr hEv, levi_add_smul (p : ℝ) hq12 hL3c, levi_add_smul (q : ℝ) hq1 hL2c,
    levi_const_mul (q : ℝ) hf1, levi_add_smul (-1) hA1c hR1c, hA1l, hR1l, hL2l, hL3l]
  ring

end GroundTheory.Heights₂.Heights.NineStatements
