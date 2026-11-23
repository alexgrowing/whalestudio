import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StatementsMuMeasureLimit
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PMuMeasureLimit
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PVertFactorPos
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PVertFactorSmooth
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PMuRegSmooth
import ReciprocityTheory.AnalyticForms.PotentialTheory.MaMeasureA
import Development.AutomorphicSpectrum.Proofs.MetricProofs.MixedIntegralTendstoOffDivisorStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.ExistsMeasurableDominatingFunctionStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.LocalSectionOfPotentialOnModelStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.RegularChartDataPropertiesStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.LocalHolomorphicSectionOfPotentialStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.MixedIntegralModelFormulaStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.RegularizedWeightPshAndBoundsStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.RegularizedWeightTendstoC2Statement
set_option maxSynthPendingDepth 1

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Giv.MuLimit

open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.ChartRestriction.G.Geo
  GroundTheory.Heights₂.Heights.LowerBoundFree

section Chart

variable {e : ℕ} {X : Type} [TopologicalSpace X]

theorem holo_cont {A : FinHolAtlas e X} {V : Set X} (hV : IsOpen V) {g : X → ℂ} (h : A.HoloOn V g) :
    ContinuousOn g V := by
  intro y hy
  obtain ⟨k, hk⟩ := A.cover y
  have hz : A.chart k y ∈ (A.chart k).target ∩ (A.chart k).symm ⁻¹' V :=
    ⟨(A.chart k).map_source hk, by
      show (A.chart k).symm (A.chart k y) ∈ V
      rw [(A.chart k).left_inv hk]; exact hy⟩
  have h1 : ContinuousAt (g ∘ (A.chart k).symm) (A.chart k y) := (h k _ hz).continuousAt
  have h2 : ContinuousAt (A.chart k) y := (A.chart k).continuousAt hk
  have h3 : ContinuousAt ((g ∘ (A.chart k).symm) ∘ (A.chart k)) y := ContinuousAt.comp h1 h2
  refine (h3.congr ?_).continuousWithinAt
  filter_upwards [(A.chart k).open_source.mem_nhds hk] with u hu
  simp [(A.chart k).left_inv hu]

theorem holo_mono {A : FinHolAtlas e X} {V W : Set X} {g : X → ℂ} (h : A.HoloOn V g) (hW : W ⊆ V) :
    A.HoloOn W g := fun j y hy => h j y ⟨hy.1, hW hy.2⟩

theorem holo_eval {σ : Type} {A : FinHolAtlas e X} {V : Set X} {s : X → σ → ℂ}
    (hs : ∀ q, A.HoloOn V fun y => s y q) (f : MvPolynomial σ ℂ) :
    A.HoloOn V fun y => eval (s y) f := by
  induction f using MvPolynomial.induction_on with
  | C a =>
    intro j y _
    simpa [Function.comp_def] using (analyticAt_const : AnalyticAt ℂ (fun _ : Fin e → ℂ => a) y)
  | add p q hp hq =>
    intro j y hy
    show AnalyticAt ℂ (fun x => eval (s ((A.chart j).symm x)) (p + q)) y
    simp only [map_add]
    exact (hp j y hy).add (hq j y hy)
  | mul_X p i hp =>
    intro j y hy
    show AnalyticAt ℂ (fun x => eval (s ((A.chart j).symm x)) (p * MvPolynomial.X i)) y
    simp only [map_mul, eval_X]
    exact (hp j y hy).mul (hs i j y hy)

theorem rsmul_one (Θ : LocPot X) : Θ.rsmul 1 = Θ := by
  cases Θ
  simp [LocPot.rsmul]

theorem mInt_zero [CompactSpace X] [T2Space X] (A : FinHolAtlas e X) (Y : Set X) (Φ : Fin e → LocPot X)
    (G : X → ℝ) (hnull : ∀ j, volume ((A.chart j).target ∩ (A.chart j).symm ⁻¹' Yᶜ) = 0)
    (hd : ∀ j, ∀ y ∈ (A.chart j).target, (A.chart j).symm y ∈ Y → 0 ≤ locDens A Φ j y)
    (h1 : MIntegrable A Φ fun _ => 1) (h0 : mInt A Φ (fun _ => 1) = 0) : mInt A Φ G = 0 := by
  classical
  unfold mInt at h0 ⊢
  split_ifs at h0 ⊢ with hP
  swap
  · rfl
  set P := hP.some with hPdef
  unfold integralWith at h0 ⊢
  have hT : ∀ j, MeasurableSet (A.chart j).target := fun j => (A.chart j).open_target.measurableSet
  have hint : ∀ j, IntegrableOn (fun y => P.χ j ((A.chart j).symm y) * 1 * locDens A Φ j y)
      (A.chart j).target := by
    intro j
    have hcl : IsCompact (tsupport (P.χ j)) := (isClosed_tsupport _).isCompact
    have hKc : IsCompact ((A.chart j) '' tsupport (P.χ j)) :=
      hcl.image_of_continuousOn ((A.chart j).continuousOn.mono (P.tsupport_subset j))
    have hKs : (A.chart j) '' tsupport (P.χ j) ⊆ (A.chart j).target :=
      Set.image_subset_iff.2 fun x hx => (A.chart j).map_source (P.tsupport_subset j hx)
    have hc : ContinuousOn (fun y => P.χ j ((A.chart j).symm y)) ((A.chart j) '' tsupport (P.χ j)) := by
      have := (P.smooth j j).continuousOn
      refine this.mono fun y hy => ⟨hKs hy, Set.mem_univ _⟩
    have hK1 : IntegrableOn (fun y => P.χ j ((A.chart j).symm y) * (1 * locDens A Φ j y))
        ((A.chart j) '' tsupport (P.χ j)) :=
      (h1 j _ hKs hKc).continuousOn_mul hc hKc
    refine IntegrableOn.of_forall_diff_eq_zero (s := (A.chart j) '' tsupport (P.χ j)) ?_ (hT j) ?_
    · simpa only [mul_assoc] using hK1
    · rintro y ⟨hy, hyK⟩
      have : (A.chart j).symm y ∉ tsupport (P.χ j) := fun h =>
        hyK ⟨_, h, (A.chart j).right_inv hy⟩
      rw [image_eq_zero_of_notMem_tsupport this]
      ring
  have hnn : ∀ j, 0 ≤ᵐ[volume.restrict (A.chart j).target]
      fun y => P.χ j ((A.chart j).symm y) * 1 * locDens A Φ j y := by
    intro j
    have hae : ∀ᵐ y ∂(volume.restrict (A.chart j).target), (A.chart j).symm y ∈ Y := by
      rw [ae_restrict_iff' (hT j)]
      refine measure_mono_null (fun y hy => ?_) (hnull j)
      simp only [Set.mem_compl_iff, Set.mem_setOf_eq, Classical.not_imp] at hy
      exact ⟨hy.1, hy.2⟩
    filter_upwards [hae, ae_restrict_mem (hT j)] with y hy hyT
    exact mul_nonneg (mul_nonneg (P.nonneg _ _) zero_le_one) (hd j y hyT hy)
  have hz : ∀ j ∈ Finset.univ, ∫ y in (A.chart j).target,
      P.χ j ((A.chart j).symm y) * 1 * locDens A Φ j y = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg fun j _ => integral_nonneg_of_ae (hnn j)).1 h0
  refine Finset.sum_eq_zero fun j hj => ?_
  have hzero := (integral_eq_zero_iff_of_nonneg_ae (hnn j) (hint j)).1 (hz j hj)
  have : (fun y => P.χ j ((A.chart j).symm y) * G ((A.chart j).symm y) * locDens A Φ j y)
      =ᵐ[volume.restrict (A.chart j).target] 0 := by
    filter_upwards [hzero] with y hy
    have hy' : P.χ j ((A.chart j).symm y) * 1 * locDens A Φ j y = 0 := hy
    show _ = (0 : ℝ)
    calc P.χ j ((A.chart j).symm y) * G ((A.chart j).symm y) * locDens A Φ j y
        = G ((A.chart j).symm y) * (P.χ j ((A.chart j).symm y) * 1 * locDens A Φ j y) := by ring
      _ = 0 := by rw [hy', mul_zero]
  rw [integral_congr_ae this]
  simp

theorem dens_nonneg (A : FinHolAtlas e X) (R : GroundTheory.Heights₂.Heights.Regular.RegChartData A) (hY : IsOpen R.Yo)
    (hp : ReciprocityTheory.AnForm.P.IsPshOn A R.Yo (R.th + LocPot.ofFun R.ph)) (j : Fin A.n) {y : Fin e → ℂ}
    (hy : y ∈ (A.chart j).target) (hyY : (A.chart j).symm y ∈ R.Yo) :
    0 ≤ locDens A (fun _ => R.th + LocPot.ofFun R.ph) j y := by
  refine ReciprocityTheory.AnForm.A.maDens_nonneg_of_posSemidef _ y fun _ => ?_
  have ho : IsOpen ((A.chart j).target ∩ (A.chart j).symm ⁻¹' R.Yo) :=
    (A.chart j).isOpen_inter_preimage_symm hY
  have h2 : ContDiffAt ℝ 2 (R.ph ∘ (A.chart j).symm) y :=
    ((R.ph_smooth j).contDiffAt (ho.mem_nhds ⟨hy, hyY⟩)).of_le
      (by first | simp | exact_mod_cast (le_top : ((2 : ℕ) : ℕ∞) ≤ ⊤) | exact WithTop.coe_le_coe.mpr le_top)
  have h1 := pot_contDiffAt_two R.th_pot ((A.chart j).symm y) j hy (R.th.mem_U _)
  refine hessC_posSemidef_of_levi _ y (h1.add h2) fun w => ?_
  exact hp _ j y ⟨hy, ⟨R.th.mem_U _, Set.mem_univ _⟩, hyY⟩ w

end Chart

section HidaSetting

variable {II : IntersectionSystem} {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {K : Type} [Fintype K] {ι : K → Type}
  [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω] [Algebra ℚ Ω] {E : Ψ → Type} [∀ τ, AddCommGroup (E τ)]
  [∀ τ, Module Ω (E τ)] {D : ComponentData II Ψ K ι Ω E} {O Lt : Type} [CommRing O] [AddCommGroup Lt] [Module O Lt]

theorem vert_re (M : XModel D) {p : ℕ} (hp : p ∈ D.S) {U : Set M.Xc} (hU : IsOpen U)
    {s : M.Xc → (Σ k, ι k) → ℂ} (hs : ∀ y ∈ U, s y ∈ mcPts (mCoordIdeal D.y))
    (hh : ∀ q, M.atlas.HoloOn U fun y => s y q) {y₀ : M.Xc} (hy : y₀ ∈ U) :
    ∃ W : Set M.Xc, IsOpen W ∧ y₀ ∈ W ∧ W ⊆ U ∧ ∃ G : M.Xc → ℂ, M.atlas.HoloOn W G ∧
      ∀ y ∈ W, Real.log (D.vertFactor p (s y)) = (G y).re := by
  obtain ⟨dG, dH, Gp, Hp, hG, hH, hdeg, hrel, hHz⟩ := VertFactorSmooth.exists_forms D hp (hs y₀ hy)
  set a : M.Xc → ℂ := fun y => eval (s y) (map (Int.castRingHom ℂ) Gp) with ha
  set b : M.Xc → ℂ := fun y => eval (s y) (map (Int.castRingHom ℂ) Hp) with hb
  have haH : M.atlas.HoloOn U a := holo_eval hh _
  have hbH : M.atlas.HoloOn U b := holo_eval hh _
  have hvf : ∀ y ∈ U, b y ≠ 0 → D.vertFactor p (s y) = ‖a y / b y‖ := fun y hyU hb0 =>
    VertFactorSmooth.vertFactor_eq D hp (hs y hyU) hG hH hdeg hrel hb0
  have hpos := VertFactorPos.proof II Ψ K ι Ω E D p hp (s y₀) (hs y₀ hy)
  set v : ℂ := a y₀ / b y₀ with hv
  have hv0 : v ≠ 0 := by
    intro h0
    rw [hvf y₀ hy hHz, ← hv, h0, norm_zero] at hpos
    exact lt_irrefl _ hpos
  have hU1 : IsOpen (U ∩ b ⁻¹' {0}ᶜ) :=
    (holo_cont hU hbH).isOpen_inter_preimage hU isOpen_compl_singleton
  set u : M.Xc → ℂ := fun y => a y / b y / v with hu
  have hcu : ContinuousOn u (U ∩ b ⁻¹' {0}ᶜ) :=
    (((holo_cont hU haH).mono Set.inter_subset_left).div ((holo_cont hU hbH).mono Set.inter_subset_left)
      fun y hy => hy.2).div_const v
  have hW : IsOpen ((U ∩ b ⁻¹' {0}ᶜ) ∩ u ⁻¹' Metric.ball 1 1) :=
    hcu.isOpen_inter_preimage hU1 Metric.isOpen_ball
  refine ⟨_, hW, ⟨⟨hy, hHz⟩, ?_⟩, fun y hy => hy.1.1,
    fun y => Complex.log (u y) + ((Real.log ‖v‖ : ℝ) : ℂ), ?_, ?_⟩
  · show u y₀ ∈ Metric.ball 1 1
    have : u y₀ = 1 := div_self hv0
    rw [this]
    exact Metric.mem_ball_self one_pos
  · intro j y hyW
    have hyU : (M.atlas.chart j).symm y ∈ U := hyW.2.1.1
    have hb0 : b ((M.atlas.chart j).symm y) ≠ 0 := hyW.2.1.2
    have hA : AnalyticAt ℂ (a ∘ (M.atlas.chart j).symm) y := haH j y ⟨hyW.1, hyU⟩
    have hB : AnalyticAt ℂ (b ∘ (M.atlas.chart j).symm) y := hbH j y ⟨hyW.1, hyU⟩
    have hUa : AnalyticAt ℂ (fun x => u ((M.atlas.chart j).symm x)) y :=
      (hA.div hB hb0).div analyticAt_const hv0
    have hslit : u ((M.atlas.chart j).symm y) ∈ Complex.slitPlane := by
      have hm : u ((M.atlas.chart j).symm y) ∈ Metric.ball (1 : ℂ) 1 := hyW.2.2
      rw [Metric.mem_ball, Complex.dist_eq] at hm
      left
      have := Complex.abs_re_le_norm (u ((M.atlas.chart j).symm y) - 1)
      have h2 := abs_lt.1 (lt_of_le_of_lt this hm)
      simp only [Complex.sub_re, Complex.one_re] at h2
      linarith [h2.1]
    exact (hUa.clog hslit).add analyticAt_const
  · intro y hyW
    have hyU : y ∈ U := hyW.1.1
    have hb0 : b y ≠ 0 := hyW.1.2
    have hm : u y ∈ Metric.ball (1 : ℂ) 1 := hyW.2
    have hu0 : u y ≠ 0 := by
      intro h0
      rw [h0, Metric.mem_ball, dist_zero_left, norm_one] at hm
      exact lt_irrefl _ hm
    have hab : a y / b y = u y * v := by
      simp only [hu]
      field_simp
    rw [hvf y hyU hb0, hab, norm_mul, Real.log_mul (norm_ne_zero_iff.2 hu0) (norm_ne_zero_iff.2 hv0)]
    simp [Complex.log_re]

theorem vert_sum_re (M : XModel D) (T : Finset ℕ) (hT : T ⊆ D.S) {U : Set M.Xc} (hU : IsOpen U)
    {s : M.Xc → (Σ k, ι k) → ℂ} (hs : ∀ y ∈ U, s y ∈ mcPts (mCoordIdeal D.y))
    (hh : ∀ q, M.atlas.HoloOn U fun y => s y q) {y₀ : M.Xc} (hy : y₀ ∈ U) :
    ∃ W : Set M.Xc, IsOpen W ∧ y₀ ∈ W ∧ W ⊆ U ∧ ∃ G : M.Xc → ℂ, M.atlas.HoloOn W G ∧
      ∀ y ∈ W, ∑ p ∈ T, Real.log (D.vertFactor p (s y)) = (G y).re := by
  classical
  induction T using Finset.induction_on with
  | empty =>
    refine ⟨U, hU, hy, subset_rfl, fun _ => 0, ?_, by simp⟩
    intro j y _
    exact analyticAt_const
  | insert r T hr ih =>
    obtain ⟨W₁, hW₁, hy₁, hs₁, G₁, hG₁, e₁⟩ := vert_re M (hT (Finset.mem_insert_self r T)) hU hs hh hy
    obtain ⟨W₂, hW₂, hy₂, hs₂, G₂, hG₂, e₂⟩ := ih fun q hq => hT (Finset.mem_insert_of_mem hq)
    refine ⟨W₁ ∩ W₂, hW₁.inter hW₂, ⟨hy₁, hy₂⟩, Set.inter_subset_left.trans hs₁, fun y => G₁ y + G₂ y, ?_, ?_⟩
    · intro j y hyW
      exact (hG₁ j y ⟨hyW.1, hyW.2.1⟩).add (hG₂ j y ⟨hyW.1, hyW.2.2⟩)
    · intro y hyW
      rw [Finset.sum_insert hr, e₁ y hyW.1, e₂ y hyW.2, Complex.add_re]

theorem log_muReg (X : ComponentSetting D O Lt) (B : ℕ) (t : ℝ) {z : (Σ k, ι k) → ℂ}
    (hz : z ∈ mcPts (mCoordIdeal D.y)) :
    Real.log ((muReg X.H X.S B t).h z) =
      Real.log (X.S.ref.h z) + X.S.regWeight t (X.M.proj z) + ∑ p ∈ D.SB B, Real.log (D.vertFactor p z) := by
  have hV := VertFactorPos.proof II Ψ K ι Ω E D
  have hVS := VertFactorSmooth.proof VertFactorPos.proof II Ψ K ι Ω E D
  have hPm : IsMultiHomogIdeal (mCoordIdeal D.y) := D.arith.2.1.2.1
  set F : ((Σ k, ι k) → ℂ) → ℝ := fun z =>
    X.S.ref.h z * Real.exp (X.S.regWeight t (X.M.proj z)) * ∏ p ∈ D.SB B, D.vertFactor p z with hFdef
  have hpos : ∀ z ∈ mcPts (mCoordIdeal D.y), 0 < F z := fun z hz =>
    mul_pos (mul_pos (X.S.ref.pos z hz.1) (Real.exp_pos _))
      (Finset.prod_pos fun p hp => hV p (Finset.mem_filter.1 hp).1 z hz)
  have hhom : ∀ z ∈ mcPts (mCoordIdeal D.y), ∀ c : K → ℂ, (∀ k, c k ≠ 0) →
      F (torusSmul c z) = (∏ k, ‖c k‖ ^ muTwDeg X.H B k) * F z := by
    intro z hz c hc
    have hcz : torusSmul c z ∈ mcPts (mCoordIdeal D.y) := mcPts_smul hPm c hc hz
    have hproj : X.M.proj (torusSmul c z) = X.M.proj z :=
      ((X.M.fibre z hz _ hcz).2 ⟨c, hc, rfl⟩).symm
    have href : X.S.ref.h (torusSmul c z) = (∏ k, ‖c k‖ ^ X.H.aMu k) * X.S.ref.h z := by
      rw [show torusSmul c z = fun p => c p.1 * z p from rfl, X.S.ref.smul c z hc, X.S.ref_deg]
      rfl
    have hvf : ∏ p ∈ D.SB B, D.vertFactor p (torusSmul c z) =
        (∏ p ∈ D.SB B, ∏ k, ‖c k‖ ^ D.vdeg p k) * ∏ p ∈ D.SB B, D.vertFactor p z := by
      rw [← Finset.prod_mul_distrib]
      exact Finset.prod_congr rfl fun p hp => (hVS p (Finset.mem_filter.1 hp).1).1 z hz c hc
    simp only [hFdef]
    rw [href, hproj, hvf, muTwDeg, MuRegSmooth.prod_norm_zpow_add_sum hc]
    ring
  have hmain : (muReg X.H X.S B t).h z = F z := by
    unfold muReg
    rw [smoothRep_h _ hz]
    obtain ⟨c, hc, hzc⟩ := exists_eq_smul_orbitRep z
    have hw0 := TopNPoly.orbitRep_blocks hz.1
    have hwP : orbitRep z ∈ mcPts (mCoordIdeal D.y) := by
      have h := mcPts_smul hPm (fun k => (c k)⁻¹) (fun k => inv_ne_zero (hc k)) hz
      convert h using 1
      funext p
      have hp : z p = c p.1 * orbitRep z p := congrFun hzc p
      rw [hp, ← mul_assoc, inv_mul_cancel₀ (hc _), one_mul]
    have hG0 : 0 < X.S.ref.h (orbitRep z) * Real.exp (X.S.regWeight t (X.M.proj (orbitRep z))) :=
      mul_pos (X.S.ref.pos _ hw0) (Real.exp_pos _)
    have hreg : (X.S.regLine t).h (orbitRep z) =
        X.S.ref.h (orbitRep z) * Real.exp (X.S.regWeight t (X.M.proj (orbitRep z))) :=
      TopNPoly.hermOfFun_h_orbitRep hz.1 hG0
    have hFw : (X.S.regLine t).h (orbitRep z) * ∏ p ∈ D.SB B, D.vertFactor p (orbitRep z) = F (orbitRep z) := by
      rw [hreg]
    rw [TopNPoly.hermOfFun_h_smul hc hzc hz.1 (by rw [hFw]; exact hpos _ hwP), hFw]
    conv_rhs => rw [hzc]
    exact (hhom _ hwP c hc).symm
  have hvpos : ∀ p ∈ D.SB B, D.vertFactor p z ≠ 0 := fun p hp =>
    (hV p (Finset.mem_filter.1 hp).1 z hz).ne'
  rw [hmain]
  simp only [hFdef]
  rw [Real.log_mul (mul_pos (X.S.ref.pos z hz.1) (Real.exp_pos _)).ne'
    (Finset.prod_ne_zero_iff.2 hvpos), Real.log_mul (X.S.ref.pos z hz.1).ne' (Real.exp_pos _).ne',
    Real.log_exp, Real.log_prod hvpos]

theorem mem_Xo (X : ComponentSetting D O Lt) {z : (Σ k, ι k) → ℂ} (hz : z ∈ mcPts (mCoordIdeal D.y))
    (hY : X.M.proj z ∈ X.S.R.Yo) : z ∈ D.Xo := by
  obtain ⟨z', ⟨hz'X, hz'm⟩, hpz⟩ := X.S.Yo_sub _ hY
  obtain ⟨c, hc, hzc⟩ := (X.M.fibre z' hz'm z hz).1 hpz
  refine ⟨hz, fun hB => hz'X.2 ?_⟩
  have h := D.bd_torus z hB (fun k => (c k)⁻¹) (fun k => inv_ne_zero (hc k))
  convert h using 1
  funext p
  rw [hzc]
  show z' p = (c p.1)⁻¹ * (c p.1 * z' p)
  rw [← mul_assoc, inv_mul_cancel₀ (hc _), one_mul]

theorem rel_reg (X : ComponentSetting D O Lt) (B : ℕ) (t : ℝ) (x y₀ : X.M.Xc) (hop : IsOpen X.S.R.Yo)
    (hy : y₀ ∈ (X.S.R.th + LocPot.ofFun (X.S.regWeight t)).U x ∩ X.S.R.Yo) :
    ∃ U : Set X.M.Xc, IsOpen U ∧ y₀ ∈ U ∧ U ⊆ (X.S.R.th + LocPot.ofFun (X.S.regWeight t)).U x ∩ X.S.R.Yo ∧
      ∃ s : X.M.Xc → (Σ k, ι k) → ℂ, (∀ y' ∈ U, s y' ∈ mcPts (mCoordIdeal D.y) ∧ X.M.proj (s y') = y') ∧
        (∀ p, X.M.atlas.HoloOn U fun y' => s y' p) ∧ ∃ G : X.M.Xc → ℂ, X.M.atlas.HoloOn U G ∧
          ∀ y' ∈ U, (X.S.R.th + LocPot.ofFun (X.S.regWeight t)).φ x y' -
            (fun z => (1 : ℝ) * Real.log ((muReg X.H X.S B t).h z)) (s y') = (G y').re := by
  obtain ⟨U₀, hU₀, hy₀, hsub, s, hs, hh, G₀, hG₀, e₀⟩ := X.S.th_ref x y₀ hy.1.1
  obtain ⟨W, hW, hyW, hWU, G₁, hG₁, e₁⟩ := vert_sum_re X.M (D.SB B) (Finset.filter_subset _ _) hU₀
    (fun y hy => (hs y hy).1) hh hy₀
  refine ⟨W ∩ X.S.R.Yo, hW.inter hop, ⟨hyW, hy.2⟩, fun y hy' => ⟨⟨hsub (hWU hy'.1), Set.mem_univ _⟩, hy'.2⟩,
    s, fun y hy' => hs y (hWU hy'.1), fun p => holo_mono (hh p) fun y hy' => hWU hy'.1,
    fun y => G₀ y - G₁ y, ?_, ?_⟩
  · intro j y hyW'
    exact (hG₀ j y ⟨hyW'.1, hWU hyW'.2.1⟩).sub (hG₁ j y ⟨hyW'.1, hyW'.2.1⟩)
  · intro y hy'
    have h1 := e₀ y (hWU hy'.1)
    have h2 := e₁ y hy'.1
    have h3 := log_muReg X B t (hs y (hWU hy'.1)).1
    rw [(hs y (hWU hy'.1)).2] at h3
    show X.S.R.th.φ x y + X.S.regWeight t y - 1 * Real.log ((muReg X.H X.S B t).h (s y)) = _
    rw [h3, Complex.sub_re, ← h1, ← h2]
    ring

theorem rel_line (X : ComponentSetting D O Lt) (x y₀ : X.M.Xc) (hop : IsOpen X.S.R.Yo)
    (hy : y₀ ∈ (X.S.R.th + LocPot.ofFun X.S.R.ph).U x ∩ X.S.R.Yo) :
    ∃ U : Set X.M.Xc, IsOpen U ∧ y₀ ∈ U ∧ U ⊆ (X.S.R.th + LocPot.ofFun X.S.R.ph).U x ∩ X.S.R.Yo ∧
      ∃ s : X.M.Xc → (Σ k, ι k) → ℂ, (∀ y' ∈ U, s y' ∈ mcPts (mCoordIdeal D.y) ∧ X.M.proj (s y') = y') ∧
        (∀ p, X.M.atlas.HoloOn U fun y' => s y' p) ∧ ∃ G : X.M.Xc → ℂ, X.M.atlas.HoloOn U G ∧
          ∀ y' ∈ U, (X.S.R.th + LocPot.ofFun X.S.R.ph).φ x y' -
            (fun z => (1 : ℝ) * Real.log ((muLine X.H).h z)) (s y') = (G y').re := by
  obtain ⟨U₀, hU₀, hy₀, hsub, s, hs, hh, G₀, hG₀, e₀⟩ := X.S.th_ref x y₀ hy.1.1
  refine ⟨U₀ ∩ X.S.R.Yo, hU₀.inter hop, ⟨hy₀, hy.2⟩, fun y hy' => ⟨⟨hsub hy'.1, Set.mem_univ _⟩, hy'.2⟩,
    s, fun y hy' => hs y hy'.1, fun p => holo_mono (hh p) fun y hy' => hy'.1, G₀,
    holo_mono hG₀ fun y hy' => hy'.1, ?_⟩
  intro y hy'
  have hm := (hs y hy'.1).1
  have hp := (hs y hy'.1).2
  have hYs : X.M.proj (s y) ∈ X.S.R.Yo := by rw [hp]; exact hy'.2
  have h1 := e₀ y hy'.1
  have h2 := X.S.ph_eq (s y) ⟨mem_Xo X hm hYs, hm⟩ hYs
  rw [hp] at h2
  show X.S.R.th.φ x y + X.S.R.ph y - 1 * Real.log ((muLine X.H).h (s y)) = _
  rw [h2, ← h1]
  ring

end HidaSetting

section Core

variable {II : IntersectionSystem} {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {K : Type} [Fintype K] {ι : K → Type}
  [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω] [Algebra ℚ Ω] {E : Ψ → Type} [∀ τ, AddCommGroup (E τ)]
  [∀ τ, Module Ω (E τ)] {D : ComponentData II Ψ K ι Ω E} {O Lt : Type} [CommRing O] [AddCommGroup Lt] [Module O Lt]

theorem chart_aesm {e : ℕ} {Y : Type} [TopologicalSpace Y] (A : FinHolAtlas e Y) (Yo : Set Y) (G : Y → ℝ)
    (hm : @Measurable Y ℝ (borel Y) _ (Yo.indicator G))
    (hnull : ∀ j, volume ((A.chart j).target ∩ (A.chart j).symm ⁻¹' Yoᶜ) = 0) (j : Fin A.n) :
    AEStronglyMeasurable (G ∘ (A.chart j).symm) (volume.restrict (A.chart j).target) := by
  letI : MeasurableSpace Y := borel Y
  haveI : BorelSpace Y := ⟨rfl⟩
  have hT : MeasurableSet (A.chart j).target := (A.chart j).open_target.measurableSet
  have h1 : AEMeasurable (A.chart j).symm (volume.restrict (A.chart j).target) :=
    (A.chart j).continuousOn_symm.aemeasurable hT
  have h2 : AEStronglyMeasurable (Yo.indicator G ∘ (A.chart j).symm) (volume.restrict (A.chart j).target) :=
    (hm.comp_aemeasurable h1).aestronglyMeasurable
  refine h2.congr ?_
  rw [Filter.EventuallyEq, ae_restrict_iff' hT]
  refine measure_mono_null (fun y hy => ?_) (hnull j)
  simp only [Set.mem_compl_iff, Set.mem_setOf_eq, Classical.not_imp] at hy
  refine ⟨hy.1, fun hY => hy.2 ?_⟩
  simp [Function.comp, Set.indicator_of_mem hY]

theorem core (X : ComponentSetting D O Lt) (B : ℕ) (Q : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (D.n + 1) → ℂ))
    (hQ : IsGoodProj (mCoordIdeal D.y) Q) (g : ((Σ k, ι k) → ℂ) → ℝ) (G₀ : X.M.Xc → ℝ) (Cg : ℝ)
    (hm : @Measurable X.M.Xc ℝ (borel X.M.Xc) _ (X.S.R.Yo.indicator G₀))
    (hb : ∀ x ∈ X.S.R.Yo, |G₀ x| ≤ Cg + Cg * Real.log (X.S.R.r x))
    (hg : ∀ z ∈ mcPts (mCoordIdeal D.y), X.M.proj z ∈ X.S.R.Yo → g z = G₀ (X.M.proj z)) :
    MIntegrable X.M.atlas (fun _ : Fin D.n => X.S.R.th + LocPot.ofFun X.S.R.ph) G₀ ∧
    ptsIntegralAt (mCoordIdeal D.y) Q (fun _ z => Real.log ((muLine X.H).h z)) g =
      mInt X.M.atlas (fun _ : Fin D.n => X.S.R.th + LocPot.ofFun X.S.R.ph) G₀ ∧
    Tendsto (fun t => ptsIntegralAt (mCoordIdeal D.y) Q (fun _ z => Real.log ((muReg X.H X.S B t).h z)) g)
      (𝓝[>] 0) (𝓝 (mInt X.M.atlas (fun _ : Fin D.n => X.S.R.th + LocPot.ofFun X.S.R.ph) G₀)) ∧
    (∀ j, volume ((X.M.atlas.chart j).target ∩ (X.M.atlas.chart j).symm ⁻¹' X.S.R.Yoᶜ) = 0) ∧
    (∀ j, ∀ y ∈ (X.M.atlas.chart j).target, (X.M.atlas.chart j).symm y ∈ X.S.R.Yo →
      0 ≤ locDens X.M.atlas (fun _ : Fin D.n => X.S.R.th + LocPot.ofFun X.S.R.ph) j y) := by
  obtain ⟨Θ, hΘp, hΘr⟩ := GlobalTheory.T.local_holomorphic_section_of_potential K ι (mCoordIdeal D.y) D.n X.M D.A' D.A'_pos.1
  have hΘpos := GlobalTheory.T.local_section_of_potential_on_model II Ψ K ι Ω E D X.M Θ hΘp hΘr
  obtain ⟨hPshOn, ⟨C1, hC1⟩, hPsh⟩ := GlobalTheory.T.regularized_weight_psh_and_bounds K ι (mCoordIdeal D.y) D.n X.M D.Xo (muLine X.H) X.S Θ
    X.S_tied hΘp hΘpos
  obtain ⟨hop, hnull, -, -⟩ := GlobalTheory.T.regular_chart_data_properties D.n X.M.Xc X.M.atlas X.S.R
  have hc2 := GlobalTheory.T.regularized_weight_tendsto_C2 K ι (mCoordIdeal D.y) D.n X.M D.Xo (muLine X.H) X.S X.S_tied
  set C : ℝ := |C1| + |X.S.R.Clog| + |Cg| with hC
  have hC0 : 0 ≤ C := by positivity
  have hlog : ∀ x ∈ X.S.R.Yo, 0 ≤ Real.log (X.S.R.r x) := fun x hx => Real.log_nonneg (X.S.R.one_le_r x hx)
  have hconv := GlobalTheory.T.mixed_integral_tendsto_off_divisor D.n X.M.Xc X.M.atlas X.S.R Θ hΘp hΘpos (fun _ => X.S.R.th)
    (fun _ => X.S.R.ph) (fun _ t => X.S.regWeight t) G₀ (fun _ => G₀) C (fun _ => X.S.R.th_pot)
    (fun _ => X.S.R.ph_smooth) ?_ ?_ ?_ ?_
  · obtain ⟨hI, hIt, hT⟩ := hconv
    have hae := chart_aesm X.M.atlas X.S.R.Yo G₀ hm hnull
    have hnull' : ∀ j, volume ((X.M.atlas.chart j).target ∩ (X.M.atlas.chart j).symm ⁻¹' (X.S.R.Yoᶜ ∪ ∅)) = 0 := by
      intro j
      rw [Set.union_empty]
      exact hnull j
    have hN : IsPtsNull (mCoordIdeal D.y) D.n ∅ := by
      intro Ψ' _
      simp
    have hgz : ∀ z ∈ mcPts (mCoordIdeal D.y), z ∉ (∅ : Set ((Σ k, ι k) → ℂ)) → X.M.proj z ∈ X.S.R.Yo →
        X.M.proj z ∉ (∅ : Set X.M.Xc) → g z = G₀ (X.M.proj z) := fun z hz _ hY _ => hg z hz hY
    have hsmL : ∀ (_ : Fin D.n) (x : X.M.Xc), X.M.atlas.SmoothOn ((X.S.R.th + LocPot.ofFun X.S.R.ph).U x ∩ X.S.R.Yo)
        ((X.S.R.th + LocPot.ofFun X.S.R.ph).φ x) := by
      intro _ x j
      have h1 := (X.S.R.th_pot.1 x j).mono (t := (X.M.atlas.chart j).target ∩ (X.M.atlas.chart j).symm ⁻¹'
        ((X.S.R.th + LocPot.ofFun X.S.R.ph).U x ∩ X.S.R.Yo)) fun y hy => ⟨hy.1, hy.2.1.1⟩
      have h2 := (X.S.R.ph_smooth j).mono (t := (X.M.atlas.chart j).target ∩ (X.M.atlas.chart j).symm ⁻¹'
        ((X.S.R.th + LocPot.ofFun X.S.R.ph).U x ∩ X.S.R.Yo)) fun y hy => ⟨hy.1, hy.2.2⟩
      exact h1.add h2
    have pushL := GlobalTheory.T.mixed_integral_model_formula K ι (mCoordIdeal D.y) D.n X.M Q X.S.R.Yo ∅ ∅ (fun _ => 1) (fun _ => muLine X.H)
      (fun _ => X.S.R.th + LocPot.ofFun X.S.R.ph) g G₀ D.arith hQ hop hnull' hN hsmL
      (fun _ x y₀ hy => rel_line X x y₀ hop hy) hgz hae
    refine ⟨hI, ?_, ?_, hnull, fun j y hy hY => dens_nonneg _ _ hop hPshOn j hy hY⟩
    · simpa only [one_mul] using (pushL.2.2 hI).2
    · refine hT.congr' ?_
      filter_upwards [hIt, hC1] with t ht htC
      have hsmR : ∀ (_ : Fin D.n) (x : X.M.Xc), X.M.atlas.SmoothOn ((X.S.R.th + LocPot.ofFun (X.S.regWeight t)).U x ∩ X.S.R.Yo)
          ((X.S.R.th + LocPot.ofFun (X.S.regWeight t)).φ x) := by
        intro _ x j
        have h1 := (X.S.R.th_pot.1 x j).mono (t := (X.M.atlas.chart j).target ∩ (X.M.atlas.chart j).symm ⁻¹'
          ((X.S.R.th + LocPot.ofFun (X.S.regWeight t)).U x ∩ X.S.R.Yo)) fun y hy => ⟨hy.1, hy.2.1.1⟩
        have h2 := (htC.1 j).mono (t := (X.M.atlas.chart j).target ∩ (X.M.atlas.chart j).symm ⁻¹'
          ((X.S.R.th + LocPot.ofFun (X.S.regWeight t)).U x ∩ X.S.R.Yo)) fun y hy => ⟨hy.1, Set.mem_univ _⟩
        exact h1.add h2
      have pushR := GlobalTheory.T.mixed_integral_model_formula K ι (mCoordIdeal D.y) D.n X.M Q X.S.R.Yo ∅ ∅ (fun _ => 1)
        (fun _ => muReg X.H X.S B t) (fun _ => X.S.R.th + LocPot.ofFun (X.S.regWeight t)) g G₀ D.arith hQ hop
        hnull' hN hsmR (fun _ x y₀ hy => rel_reg X B t x y₀ hop hy) hgz hae
      have := (pushR.2.2 ht).2
      simp only [one_mul] at this
      exact this.symm
  · have hP1 := hPsh 1 one_pos
    filter_upwards [hC1, hP1] with t ht hp
    intro _
    refine ⟨ht.1, ?_, fun x hx => ?_⟩
    · rw [rsmul_one] at hp
      exact hp
    · have h1 := (ht.2 x hx).1
      have h2 := (ht.2 x hx).2
      have h3 := X.S.R.ph_ge x hx
      have hL := hlog x hx
      have hC1C : C1 ≤ C := by
        have := le_abs_self C1
        have := abs_nonneg X.S.R.Clog
        have := abs_nonneg Cg
        linarith
      have hCl : |X.S.R.Clog| ≤ C := by
        have := abs_nonneg C1
        have := abs_nonneg Cg
        linarith
      have hCL : 0 ≤ C * Real.log (X.S.R.r x) := mul_nonneg hC0 hL
      have h4 : X.S.R.Clog * Real.log (X.S.R.r x) ≤ C * Real.log (X.S.R.r x) :=
        mul_le_mul_of_nonneg_right ((le_abs_self _).trans hCl) hL
      refine ⟨abs_le.2 ⟨?_, ?_⟩, ?_⟩
      · nlinarith
      · linarith
      · linarith
  · intro _ j K' hK' hKc
    exact hc2 j K' hK' hKc
  · refine Filter.Eventually.of_forall fun _ => ⟨hm, fun x hx => ?_⟩
    have hL := hlog x hx
    have hCg : Cg ≤ C := by
      have := le_abs_self Cg
      have := abs_nonneg C1
      have := abs_nonneg X.S.R.Clog
      linarith
    have := mul_le_mul_of_nonneg_right hCg hL
    linarith [hb x hx]
  · intro K' _ _
    intro u hu
    exact Filter.Eventually.of_forall fun _ x _ => by simpa using mem_uniformity_of_eq hu rfl

end Core

end GlobalTheory.CompanionTheory.Ar.Giv.MuLimit

namespace GlobalTheory.CompanionTheory.Ar.Giv

open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.ChartRestriction.G.Geo
  GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar.Giv.MuLimit

theorem muMeasureLimit : GroundTheory.Heights₂.Heights.LowerBoundFree.MuMeasureLimit.Statement := by
  intro II Ψ _ _ K _ ι _ Ω _ _ E _ _ D O Lt _ _ _ X B _ _
  classical
  by_cases hΨ : ∃ Q : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (D.n + 1) → ℂ), IsGoodProj (mCoordIdeal D.y) Q
  swap
  · have h0 : ∀ (φ : Fin D.n → ((Σ k, ι k) → ℂ) → ℝ) (g : ((Σ k, ι k) → ℂ) → ℝ),
        ptsIntegral (e := D.n) (mCoordIdeal D.y) φ g = 0 := fun φ g => by
      unfold ptsIntegral
      rw [dif_neg hΨ]
    have hd : degMu X.H = 0 := h0 _ _
    have hg : ∀ t, geomDeg (mCoordIdeal D.y) (muReg X.H X.S B t) D.n = 0 := fun t => h0 _ _
    refine ⟨?_, ?_⟩
    · simp only [h0, hd, mul_zero, zero_div]
      exact tendsto_const_nhds
    · simp only [hg, hd]
      exact tendsto_const_nhds
  · have hat : ∀ (φ : Fin D.n → ((Σ k, ι k) → ℂ) → ℝ) (g : ((Σ k, ι k) → ℂ) → ℝ),
        ptsIntegral (e := D.n) (mCoordIdeal D.y) φ g =
          ptsIntegralAt (mCoordIdeal D.y) hΨ.choose φ g := fun φ g => by
      unfold ptsIntegral
      rw [dif_pos hΨ]
    obtain ⟨G, Cg, hm, hb, hG⟩ := GlobalTheory.T.cuspWeight_factors_through_measurable_log_bounded II Ψ K ι Ω E D O Lt X
    have hCg : ∀ x ∈ X.S.R.Yo, |G x / 2| ≤ |Cg| + |Cg| * Real.log (X.S.R.r x) := by
      intro x hx
      have hL : 0 ≤ Real.log (X.S.R.r x) := Real.log_nonneg (X.S.R.one_le_r x hx)
      have h1 := hb x hx
      have h2 : Cg * Real.log (X.S.R.r x) ≤ |Cg| * Real.log (X.S.R.r x) :=
        mul_le_mul_of_nonneg_right (le_abs_self _) hL
      have h3 := le_abs_self Cg
      have h4 := abs_nonneg (G x)
      have h5 : 0 ≤ |Cg| * Real.log (X.S.R.r x) := mul_nonneg (abs_nonneg _) hL
      rw [abs_div, abs_two]
      linarith
    have hm2 : @Measurable X.M.Xc ℝ (borel X.M.Xc) _ (X.S.R.Yo.indicator fun x => G x / 2) := by
      have : (X.S.R.Yo.indicator fun x => G x / 2) = fun x => X.S.R.Yo.indicator G x / 2 := by
        funext x
        by_cases hx : x ∈ X.S.R.Yo <;> simp [hx]
      rw [this]
      letI : MeasurableSpace X.M.Xc := borel X.M.Xc
      exact hm.div_const 2
    have hm1 : @Measurable X.M.Xc ℝ (borel X.M.Xc) _ (X.S.R.Yo.indicator fun _ => (1 : ℝ)) := by
      letI : MeasurableSpace X.M.Xc := borel X.M.Xc
      haveI : BorelSpace X.M.Xc := ⟨rfl⟩
      exact measurable_const.indicator (GlobalTheory.T.regular_chart_data_properties D.n X.M.Xc X.M.atlas X.S.R).1.measurableSet
    obtain ⟨-, cU, tU, hnull, hdens⟩ := core X B hΨ.choose hΨ.choose_spec (fun z => X.Cd.cuspWeight z / 2)
      (fun x => G x / 2) |Cg| hm2 hCg (fun z hz hY => by rw [hG z hz hY])
    obtain ⟨hI1, c1, t1, -, -⟩ := core X B hΨ.choose hΨ.choose_spec (fun _ => 1) (fun _ => 1) 1 hm1
      (fun x hx => by
        have hL : 0 ≤ Real.log (X.S.R.r x) := Real.log_nonneg (X.S.R.one_le_r x hx)
        simp only [abs_one, one_mul]
        linarith) (fun _ _ _ => rfl)
    have hdeg : degMu X.H = mInt X.M.atlas (fun _ : Fin D.n => X.S.R.th + LocPot.ofFun X.S.R.ph) fun _ => 1 := by
      show ptsIntegral (e := D.n) (mCoordIdeal D.y) _ _ = _
      rw [hat]
      exact c1
    have hhalf : meanU X.H X.Cd * degMu X.H / 2 =
        mInt X.M.atlas (fun _ : Fin D.n => X.S.R.th + LocPot.ofFun X.S.R.ph) fun x => G x / 2 := by
      by_cases hd : degMu X.H = 0
      · rw [hd, mul_zero, zero_div]
        exact (mInt_zero _ _ _ _ hnull hdens hI1 (hdeg ▸ hd)).symm
      · have h2 := ptsIntegral_div_two (e := D.n) (mCoordIdeal D.y) (fun _ => phMu X.H) X.Cd.cuspWeight
        unfold meanU
        rw [div_mul_cancel₀ _ hd, ← h2, hat]
        exact cU
    refine ⟨?_, ?_⟩
    · rw [hhalf]
      simp only [hat]
      exact tU
    · rw [hdeg]
      unfold geomDeg
      simp only [hat]
      exact t1

end GlobalTheory.CompanionTheory.Ar.Giv
