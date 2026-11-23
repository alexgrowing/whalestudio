import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.PotentialsBoundedRegSettingEqReference
import GroundTheory.HeightsAndTheta.Heights.Regularisation.BoundedStatements
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterNamed
import Development.AutomorphicSpectrum.Proofs.MetricProofs.PositionPot
import Development.AutomorphicSpectrum.Proofs.MetricProofs.FubiniStudyMetricSmooth
import Development.AutomorphicSpectrum.Proofs.MetricProofs.RegularizedWeightPshAndBoundsStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.RegularizedWeightTendstoC2Statement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.MixedIntegralTendstoOffDivisorStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.RegularChartDataPropertiesStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.LocalHolomorphicSectionOfPotentialStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.IntersectionNumberMetricChangeStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.RegularizedHodgeMetricSmoothStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.VerticalHodgeMetricLogFormulaStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.ExistsContinuousMetricRatioStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.ExistsPositivePotentialDominatingStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.RegularizedWeightTendstoUniformlyStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.SmoothOnAtlasContinuousStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.RegularizedHodgeHeightLimitStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp
open ReciprocityTheory.AnForm (levi)

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Cusp
open MvPolynomial MeasureTheory ReciprocityTheory.AnForm.M

section Main
variable {K : Type} [Fintype K] {J : K → Type} [∀ k, Fintype (J k)] {II : IntersectionSystem} {Ψ : Type} [Fintype Ψ]
  {Ω : Type} [Field Ω] [Algebra ℚ Ω] {W : Ψ → Type} [∀ τ, AddCommGroup (W τ)] [∀ τ, Module Ω (W τ)]
  {D : ComponentData II Ψ K J Ω W}

theorem tuo_const {A₁ B₁ C₂ : Type*} [UniformSpace B₁] (l : Filter C₂) (f : A₁ → B₁) (s : Set A₁) :
    TendstoUniformlyOn (fun _ : C₂ => f) f l s :=
  fun _ hu => Filter.Eventually.of_forall fun _ _ _ => refl_mem_uniformity hu

theorem mem_Xo_of_proj_mem {Hd : HodgeData D} {M : XModel D} (S : LogLogRegularisationSetting M D.Xo (muLine Hd))
    {z : (Σ k, J k) → ℂ} (hz : z ∈ mcPts (mCoordIdeal D.y)) (hY : M.proj z ∈ S.R.Yo) : z ∈ D.Xo := by
  obtain ⟨z', ⟨hz'X, hz'P⟩, hz'⟩ := S.Yo_sub _ hY
  obtain ⟨c, hc, hzc⟩ := (M.fibre z' hz'P z hz).1 hz'
  refine ⟨hz, fun hB => ?_⟩
  have hinv : ∀ k, (c k)⁻¹ ≠ 0 := fun k => inv_ne_zero (hc k)
  have h1 := D.bd_torus z hB (fun k => (c k)⁻¹) hinv
  have h2 : torusSmul (fun k => (c k)⁻¹) z = z' := by
    funext p
    rw [hzc]
    simp [torusSmul, inv_mul_cancel_left₀ (hc p.1)]
  rw [h2] at h1
  exact hz'X.2 h1

theorem tendsto_arLimFun (hLoc : ReciprocityTheory.ChartRestriction.G.AI.I2.MetricLocalStatement) {Hd : HodgeData D} {M : XModel D}
    (S : LogLogRegularisationSetting M D.Xo (muLine Hd)) (hS : S.IsTied) (B : ℕ) (hII : IsFullIntersectionSystem II)
    (Nb : HermLine J) (hNb : IsSmoothHerm Nb) (hNa : Nb.a = muTwDeg Hd B) :
    Tendsto (arLimFun Hd S B) (𝓝[>] 0) (𝓝 (limTop Hd B Nb)) := by
  obtain ⟨Pn, hPn, hPnS⟩ := GlobalTheory.T.local_holomorphic_section_of_potential K J (mCoordIdeal D.y) D.n M Nb hNb
  obtain ⟨Θ, hΘ, hΘp, hΘN⟩ := GlobalTheory.T.exists_positive_potential_dominating K J II Ψ Ω W D M Pn hPn
  obtain ⟨-, ⟨C₁, hC₁⟩, hpsh⟩ := GlobalTheory.T.regularized_weight_psh_and_bounds K J (mCoordIdeal D.y) D.n M D.Xo (muLine Hd) S Θ hS hΘ hΘp
  obtain ⟨κ, hκc, hκ⟩ := GlobalTheory.T.exists_continuous_metric_ratio K J II Ψ Ω W D Hd M S B Nb hNb hNa
  obtain ⟨Bκ, hBκ⟩ : ∃ b : ℝ, ∀ x, |κ x| ≤ b := by
    obtain ⟨b, hb⟩ := (isCompact_univ.image hκc).isBounded.exists_norm_le
    exact ⟨b, fun x => hb _ ⟨x, Set.mem_univ _, rfl⟩⟩
  obtain ⟨hYo, hYnull, -, -⟩ := GlobalTheory.T.regular_chart_data_properties D.n M.Xc M.atlas S.R
  have hph := S.R.ph_smooth

  set Cc : ℝ := |C₁| + |S.R.Clog| + |Bκ| + 1 with hCc
  have hCc0 : 0 ≤ Cc := by positivity
  have hlogr : ∀ x ∈ S.R.Yo, 0 ≤ Real.log (S.R.r x) := fun x hx => Real.log_nonneg (S.R.one_le_r x hx)

  have hbd : ∀ᶠ t in 𝓝[>] (0 : ℝ), M.atlas.Smooth (S.regWeight t) ∧
      ∀ x ∈ S.R.Yo, |S.regWeight t x| ≤ |C₁| + |S.R.Clog| * Real.log (S.R.r x) ∧ S.regWeight t x ≤ |C₁| := by
    filter_upwards [hC₁] with t ht
    refine ⟨ht.1, fun x hx => ?_⟩
    obtain ⟨h1, h2⟩ := ht.2 x hx
    have h3 := S.R.ph_ge x hx
    have h4 : -(|S.R.Clog| * Real.log (S.R.r x)) ≤ -S.R.Clog * Real.log (S.R.r x) := by
      have := mul_le_mul_of_nonneg_right (le_abs_self S.R.Clog) (hlogr x hx)
      linarith
    have h5 : C₁ ≤ |C₁| := le_abs_self _
    have h6 : 0 ≤ |S.R.Clog| * Real.log (S.R.r x) := mul_nonneg (abs_nonneg _) (hlogr x hx)
    have h7 : 0 ≤ |C₁| := abs_nonneg _
    exact ⟨abs_le.2 ⟨by linarith, by linarith⟩, by linarith⟩
  set G : M.Xc → ℝ := S.R.Yo.indicator fun x => κ x - S.R.ph x with hG
  set GT : ℝ → M.Xc → ℝ := fun t x => κ x - S.regWeight t x with hGT
  have hconv : ∀ i : ℕ, MIntegrable M.atlas (positionPot S.R.th Pn S.R.ph i) G ∧
      (∀ᶠ t in 𝓝[>] (0 : ℝ), MIntegrable M.atlas (positionPot S.R.th Pn (S.regWeight t) i) (GT t)) ∧
      Tendsto (fun t => mInt M.atlas (positionPot S.R.th Pn (S.regWeight t) i) (GT t)) (𝓝[>] 0)
        (𝓝 (mInt M.atlas (positionPot S.R.th Pn S.R.ph i) G)) := by
    intro i
    refine GlobalTheory.T.mixed_integral_tendsto_off_divisor D.n M.Xc M.atlas S.R Θ hΘ hΘp
      (fun j : Fin D.n => if (j : ℕ) < i then S.R.th else Pn)
      (fun j : Fin D.n => if (j : ℕ) < i then S.R.ph else fun _ => 0)
      (fun (j : Fin D.n) t => if (j : ℕ) < i then S.regWeight t else fun _ => 0) G GT Cc
      ?_ ?_ ?_ ?_ ?_ ?_
    · intro j
      by_cases h : (j : ℕ) < i
      · simpa [h] using S.R.th_pot
      · simpa [h] using hPn
    · intro j
      by_cases h : (j : ℕ) < i
      · simpa [h] using hph
      · simp only [h, if_false]
        intro j'
        exact contDiffOn_const
    · have h1 := hpsh 1 one_pos
      filter_upwards [hbd, h1] with t ht ht1 j
      by_cases h : (j : ℕ) < i
      · simp only [h, if_true]
        refine ⟨ht.1, ?_, fun x hx => ?_⟩
        · have : Θ.rsmul 1 = Θ := by
            cases Θ
            simp [LocPot.rsmul]
          rwa [this] at ht1
        · obtain ⟨h2, h3⟩ := ht.2 x hx
          have hL := hlogr x hx
          have h4 : |S.R.Clog| * Real.log (S.R.r x) ≤ Cc * Real.log (S.R.r x) :=
            mul_le_mul_of_nonneg_right (by rw [hCc]; linarith [abs_nonneg C₁, abs_nonneg Bκ]) hL
          have h5 : |C₁| ≤ Cc := by rw [hCc]; linarith [abs_nonneg S.R.Clog, abs_nonneg Bκ]
          exact ⟨by linarith, by linarith⟩
      · simp only [h, if_false]
        refine ⟨fun j' => contDiffOn_const, hΘN, fun x hx => ?_⟩
        have hL := hlogr x hx
        have := mul_nonneg hCc0 hL
        simp only [abs_zero]
        exact ⟨by linarith, hCc0⟩
    · intro j k K' hK' hK'c
      by_cases h : (j : ℕ) < i
      · simp only [h, if_true]
        exact GlobalTheory.T.regularized_weight_tendsto_C2 K J (mCoordIdeal D.y) D.n M D.Xo (muLine Hd) S hS k K' hK' hK'c
      · simp only [h, if_false]
        exact ⟨tuo_const _ _ _, tuo_const _ _ _, tuo_const _ _ _⟩
    · filter_upwards [hbd] with t ht
      refine ⟨?_, fun x hx => ?_⟩
      · letI : MeasurableSpace M.Xc := borel M.Xc
        haveI : BorelSpace M.Xc := ⟨rfl⟩
        have hc : Continuous (GT t) := hκc.sub (GlobalTheory.T.smooth_on_atlas_continuous D.n M.Xc M.atlas _ ht.1)
        exact hc.measurable.indicator hYo.measurableSet
      · obtain ⟨h2, -⟩ := ht.2 x hx
        have hL := hlogr x hx
        have h4 : |S.R.Clog| * Real.log (S.R.r x) ≤ Cc * Real.log (S.R.r x) :=
          mul_le_mul_of_nonneg_right (by rw [hCc]; linarith [abs_nonneg C₁, abs_nonneg Bκ]) hL
        have h5 : |C₁| + |κ x| ≤ Cc := by
          have := hBκ x
          have h6 := le_abs_self Bκ
          rw [hCc]; linarith [abs_nonneg S.R.Clog]
        have h7 : |GT t x| ≤ |κ x| + |S.regWeight t x| := abs_sub _ _
        linarith
    · intro K' hK' hK'c
      have hu := GlobalTheory.T.regularized_weight_tendsto_uniformly K J (mCoordIdeal D.y) D.n M D.Xo (muLine Hd) S hS K' hK' hK'c
      have hu2 : TendstoUniformlyOn GT (fun x => κ x - S.R.ph x) (𝓝[>] 0) K' := by
        rw [Metric.tendstoUniformlyOn_iff] at hu ⊢
        intro ε hε
        filter_upwards [hu ε hε] with t ht x hx
        have := ht x hx
        simp only [hGT, Real.dist_eq] at this ⊢
        rwa [show κ x - S.R.ph x - (κ x - S.regWeight t x) = -(S.R.ph x - S.regWeight t x) by ring, abs_neg]
      exact hu2.congr_right fun x hx => by simp [hG, Set.indicator_of_mem (hK' hx)]

  have hmeasT : ∀ t, M.atlas.Smooth (S.regWeight t) → ∀ j, AEStronglyMeasurable (GT t ∘ (M.atlas.chart j).symm)
      (volume.restrict (M.atlas.chart j).target) := by
    intro t ht j
    have hc : Continuous (GT t) := hκc.sub (GlobalTheory.T.smooth_on_atlas_continuous D.n M.Xc M.atlas _ ht)
    exact (hc.comp_continuousOn (M.atlas.chart j).continuousOn_symm).aestronglyMeasurable
      (M.atlas.chart j).open_target.measurableSet
  have hmeasG : ∀ j, AEStronglyMeasurable (G ∘ (M.atlas.chart j).symm)
      (volume.restrict (M.atlas.chart j).target) := by
    intro j
    set V : Set (Fin D.n → ℂ) := (M.atlas.chart j).target ∩ (M.atlas.chart j).symm ⁻¹' S.R.Yo with hV
    have hVo : IsOpen V := (M.atlas.chart j).continuousOn_symm.isOpen_inter_preimage
      (M.atlas.chart j).open_target hYo
    have hF : ContinuousOn (fun y => κ ((M.atlas.chart j).symm y) - S.R.ph ((M.atlas.chart j).symm y)) V := by
      refine ContinuousOn.sub ?_ (hph j).continuousOn
      exact hκc.comp_continuousOn ((M.atlas.chart j).continuousOn_symm.mono Set.inter_subset_left)
    have h1 : AEStronglyMeasurable (V.indicator fun y => κ ((M.atlas.chart j).symm y) -
        S.R.ph ((M.atlas.chart j).symm y)) volume :=
      (aestronglyMeasurable_indicator_iff hVo.measurableSet).2 (hF.aestronglyMeasurable hVo.measurableSet)
    refine (h1.mono_measure Measure.restrict_le_self).congr ?_
    refine (ae_restrict_iff' (M.atlas.chart j).open_target.measurableSet).2 (Filter.Eventually.of_forall fun y hy => ?_)
    by_cases hyY : (M.atlas.chart j).symm y ∈ S.R.Yo
    · have hyV : y ∈ V := ⟨hy, hyY⟩
      simp [hG, Set.indicator_of_mem hyY, Set.indicator_of_mem hyV]
    · have hyV : y ∉ V := fun h => hyY h.2
      simp [hG, Set.indicator_of_notMem hyY, Set.indicator_of_notMem hyV]

  have hwl : ∀ i, ptsIntegral (mCoordIdeal D.y)
      (pot fun j : Fin D.n => if (j : ℕ) < i then muVert Hd B else Nb)
      (fun z => Real.log (Nb.h z) - Real.log ((muVert Hd B).h z)) =
      mInt M.atlas (positionPot S.R.th Pn S.R.ph i) G := by
    intro i
    refine GlobalTheory.T.regularized_hodge_height_limit K J II Ψ Ω W D Hd M S B Nb (muVert Hd B) Pn i S.R.ph G _ hPn hPnS hph ?_ ?_ hmeasG (hconv i).1
    · intro z hz hY
      have h1 := S.ph_eq z ⟨mem_Xo_of_proj_mem S hz hY, hz⟩ hY
      rw [GlobalTheory.T.vertical_hodge_metric_log_formula K J II Ψ Ω W D Hd B z hz, h1]
      ring
    · intro z hz hY
      have h1 := S.ph_eq z ⟨mem_Xo_of_proj_mem S hz hY, hz⟩ hY
      have h2 := GlobalTheory.T.vertical_hodge_metric_log_formula K J II Ψ Ω W D Hd B z hz
      have h3 := hκ z hz
      simp only [hG, Set.indicator_of_mem hY]
      rw [h1, h2, h3]
      ring
  have hev : ∀ᶠ t in 𝓝[>] (0 : ℝ),
      II K J (mCoordIdeal D.y) (D.n + 1) (fun _ => Nb) - ∑ i ∈ Finset.range (D.n + 1),
        mInt M.atlas (positionPot S.R.th Pn (S.regWeight t) i) (GT t) = arLimFun Hd S B t := by
    have hint : ∀ᶠ t in 𝓝[>] (0 : ℝ), ∀ i ∈ Finset.range (D.n + 1),
        MIntegrable M.atlas (positionPot S.R.th Pn (S.regWeight t) i) (GT t) :=
      (Filter.eventually_all_finset _).2 fun i _ => (hconv i).2.1
    filter_upwards [GlobalTheory.T.regularized_hodge_metric_smooth K J II Ψ Ω W D Hd M S B hS, hbd, hint] with t hsp hb hi
    obtain ⟨hsm, hdeg, hlog⟩ := hsp
    have hT := GlobalTheory.T.intersection_number_metric_change hLoc K J II (mCoordIdeal D.y) D.n Nb (muReg Hd S B t) hII D.arith hNb hsm
      (hdeg.trans hNa.symm)
    rw [arLimFun, hT]
    congr 1
    refine Finset.sum_congr rfl fun i hi' => ?_
    refine (GlobalTheory.T.regularized_hodge_height_limit K J II Ψ Ω W D Hd M S B Nb (muReg Hd S B t) Pn i (S.regWeight t) (GT t) _ hPn hPnS
      (fun j => (hb.1 j).mono fun y hy => ⟨hy.1, Set.mem_univ _⟩) ?_ ?_ (hmeasT t hb.1) (hi i hi')).symm
    · intro z hz _
      exact hlog z hz
    · intro z hz _
      simp only [hGT]
      rw [hlog z hz, hκ z hz]
      ring
  have hlim : Tendsto (fun t => II K J (mCoordIdeal D.y) (D.n + 1) (fun _ => Nb) -
      ∑ i ∈ Finset.range (D.n + 1), mInt M.atlas (positionPot S.R.th Pn (S.regWeight t) i) (GT t))
      (𝓝[>] 0) (𝓝 (limTop Hd B Nb)) := by
    rw [limTop]
    simp only [hwl]
    exact tendsto_const_nhds.sub (tendsto_finset_sum _ fun i _ => (hconv i).2.2)
  exact hlim.congr' hev

theorem arLim_exists_eq : Top.Given → PtsIntegrableStatement → ∀ (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (II : IntersectionSystem) (Ψ : Type) [Fintype Ψ] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (W : Ψ → Type) [∀ τ, AddCommGroup (W τ)] [∀ τ, Module Ω (W τ)] (D : ComponentData II Ψ K J Ω W) (Hd : HodgeData D) (M M' : XModel D) (S : LogLogRegularisationSetting M D.Xo (muLine Hd)) (S₁ : LogLogRegularisationSetting M' D.Xo (muLine Hd)) (B : ℕ), IsFullIntersectionSystem II → S.IsTied → S₁.IsTied → ArLimExists Hd S B ∧ arLim Hd S B = arLim Hd S₁ B := by
  intro hG _ K _ J _ II Ψ _ Ω _ _ W _ _ D Hd M M' S S₁ B hII hS hS₁
  have hIn : PB.Inputs := hG.2.2.2.2.2.2.2.2.2.1
  have hNb : IsSmoothHerm (fsHerm J (muTwDeg Hd B)) := PB.StepW.fsHerm_isSmoothHerm K J _
  have h1 := tendsto_arLimFun hIn.metricLocal S hS B hII _ hNb rfl
  have h2 := tendsto_arLimFun hIn.metricLocal S₁ hS₁ B hII _ hNb rfl
  exact ⟨⟨_, h1⟩, by rw [arLim, arLim, h1.limUnder_eq, h2.limUnder_eq]⟩

end Main
end GlobalTheory.CompanionTheory.Ar.Cusp
