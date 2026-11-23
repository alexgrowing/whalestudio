import Development.WeilBound.CoreStatements.PlurisubharmonicCones.LevelFree
import Development.WeilBound.CoreStatements.PlurisubharmonicCones.ExistsPshPull
import Development.AutomorphicSpectrum.Proofs.MetricProofs.ChartLocalAnalyticTrivializationStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.ProjectionOfChartAnalyticStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.VerticalFactorSmoothHermitianMetricStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.HodgePotentialSmoothOffBoundaryStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.RegularizedWeightPshAndBoundsStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.ExistsPositivePotentialDominatingStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.LocalSectionVerticalFactorStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.RegularizedHodgeMetricSmoothStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.VerticalHodgeMetricLogFormulaStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.BlockPullbackHermLineStatement
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.HermitianCombinationSmoothConjStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterBridgeB

open Filter Topology ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp
open ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4 ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P GlobalTheory.CompanionTheory.Ar.Cmp

noncomputable section

namespace LevelTowerAlt.Comparison₂

variable {K : Type} [Fintype K] {J : K → Type} [∀ k, Fintype (J k)]

theorem smul_mem {P : Ideal (MRing J)} {n : ℕ} (hP : IsArithVar P n) {z : (Σ k, J k) → ℂ} (hz : z ∈ mcPts P) {c : K → ℂ}
    (hc : ∀ k, c k ≠ 0) : torusSmul c z ∈ mcPts P :=
  mem_mcPts_of_sameOrbit hP.2.1.2.1 ⟨c, hc, rfl⟩ hz

theorem proj_eq {P : Ideal (MRing J)} {n : ℕ} (M : CxModel P n) {z z' : (Σ k, J k) → ℂ} (hz : z ∈ mcPts P) (hz' : z' ∈ mcPts P) :
    M.proj z' = M.proj z ↔ SameOrbit z z' := M.fibre z' hz' z hz

variable {II : IntersectionSystem} {Ψ : Type} [Fintype Ψ] {Ω : Type} [Field Ω] [Algebra ℚ Ω] {W : Ψ → Type}
  [∀ τ, AddCommGroup (W τ)] [∀ τ, Module Ω (W τ)] (D : ComponentData II Ψ K J Ω W)

theorem bd_orbit {z z' : (Σ k, J k) → ℂ} (h : SameOrbit z z') (hz : z' ∈ D.Bd) : z ∈ D.Bd := by
  obtain ⟨c, hc, rfl⟩ := h
  exact D.bd_torus _ hz c hc

theorem exists_read {z₀ : (Σ k, J k) → ℂ} (hz₀ : z₀ ∈ mcPts (mCoordIdeal D.y)) :
    ∃ (a : Fin D.nCharts) (T : ((Σ k, J k) → ℂ) → Fin D.n → ℂ), AnalyticAt ℂ T z₀ ∧ T z₀ ∈ Metric.ball 0 1 ∧
      ∀ᶠ z in 𝓝 z₀, z ∈ mcPts (mCoordIdeal D.y) → T z ∈ Metric.ball 0 1 ∧ SameOrbit z ((D.chart a).γ (T z)) := by
  obtain ⟨a, t₀, ht₀, c, hc, rfl⟩ := D.chart_cover z₀ hz₀
  have hb : t₀ ∈ Metric.ball (0 : Fin D.n → ℂ) 1 := mem_ball_zero_iff.2 (ht₀.trans_lt (by norm_num))
  obtain ⟨V, T, hV, hm, hT, h0, h⟩ := GlobalTheory.T.chart_local_analytic_trivialization K J II Ψ Ω W D a t₀ hb
  have hs : ∀ z, AnalyticAt ℂ (torusSmul (ι := J) fun k => (c k)⁻¹) z := fun z =>
    analyticAt_pi_iff.2 fun p => analyticAt_const.mul ((ContinuousLinearMap.proj (R := ℂ) p).analyticAt z)
  have e0 : torusSmul (fun k => (c k)⁻¹) (torusSmul c ((D.chart a).γ t₀)) = (D.chart a).γ t₀ :=
    funext fun p => inv_mul_cancel_left₀ (hc _) _
  refine ⟨a, T ∘ torusSmul fun k => (c k)⁻¹, AnalyticAt.comp (by rw [e0]; exact hT _ hm) (hs _), ?_, ?_⟩
  · exact Set.mem_of_eq_of_mem ((congrArg T e0).trans h0) hb
  · filter_upwards [(hs _).continuousAt.eventually_mem (hV.mem_nhds (by rwa [e0]))] with z hz hzP
    obtain ⟨h1, c', hc', h2⟩ := h _ ⟨hz, smul_mem D.arith hzP fun k => inv_ne_zero (hc k)⟩
    refine ⟨h1, fun k => c k * c' k, fun k => mul_ne_zero (hc k) (hc' k), funext fun p => ?_⟩
    have := congrFun h2 p
    simp only [torusSmul] at this
    exact ((mul_inv_cancel_left₀ (hc _) _).symm.trans (congrArg _ this)).trans (mul_assoc _ _ _).symm

theorem contOn_Xo (Hd : HodgeData D) (ref : HermLine J) (ha : (muLine Hd).a = ref.a) (hr : IsSmoothHerm ref) :
    ContinuousOn (fun z => Real.log ((muLine Hd).h z) - Real.log (ref.h z)) D.Xo := by
  intro z₀ hz₀
  obtain ⟨a, T, hT, hb, h⟩ := exists_read D hz₀.1
  have h0 := h.self_of_nhds hz₀.1
  have hoff : T z₀ ∈ offBd D a := ⟨hb, fun hm => hz₀.2 (bd_orbit D h0.2 hm)⟩
  have h1 : ContinuousAt (fun t => phMu Hd ((D.chart a).γ t)) (T z₀) :=
    ((GlobalTheory.T.hodge_potential_smooth_off_boundary K J II Ψ Ω W D Hd).1 a).continuousOn.continuousAt ((SncPiece.isOpen_offBd D a).mem_nhds hoff)
  have hγ := ((D.chart a).analytic _ hb).continuousAt
  have hm := (D.chart a).mem _ hb
  have ho : IsOpen {z : (Σ k, J k) → ℂ | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0} := by
    simp only [Set.setOf_forall, Set.setOf_exists]
    exact isOpen_iInter_of_finite fun k => isOpen_iUnion fun i => isOpen_ne_fun (continuous_apply _) continuous_const
  have h2 : ContinuousAt (fun t => Real.log (ref.h ((D.chart a).γ t))) (T z₀) :=
    (ContinuousAt.comp (f := (D.chart a).γ) (hr.continuousOn.continuousAt (ho.mem_nhds hm.1)) hγ).log (ref.pos _ hm.1).ne'
  have h3 := (ContinuousAt.comp (f := T) (h1.sub h2) hT.continuousAt).continuousWithinAt (s := D.Xo)
  have key : ∀ z, T z ∈ Metric.ball 0 1 ∧ SameOrbit z ((D.chart a).γ (T z)) →
      Real.log ((muLine Hd).h z) - Real.log (ref.h z) =
        ((fun t => phMu Hd ((D.chart a).γ t) - Real.log (ref.h ((D.chart a).γ t))) ∘ T) z := fun z hz =>
    log_diff_orbit ha ((D.chart a).mem _ hz.1).1 hz.2
  refine h3.congr_of_eventuallyEq ?_ (key _ h0)
  filter_upwards [nhdsWithin_le_nhds h, self_mem_nhdsWithin] with z hz hz' using key z (hz hz'.1)

theorem exists_ext (Hd : HodgeData D) (M : XModel D) (S : LogLogRegularisationSetting M D.Xo (muLine Hd)) :
    ∃ (V : Set M.Xc) (g : M.Xc → ℝ), IsOpen V ∧ ContinuousOn g V ∧ (∀ x ∈ V ∩ S.R.Yo, g x = S.R.ph x) ∧
      ∀ z ∈ mcPts (mCoordIdeal D.y), (z ∉ D.Bd → M.proj z ∈ V) ∧
        g (M.proj z) = Real.log ((muLine Hd).h z) - Real.log (S.ref.h z) := by
  choose r hr hr' using M.surj
  have hg : ∀ z ∈ mcPts (mCoordIdeal D.y), Real.log ((muLine Hd).h (r (M.proj z))) - Real.log (S.ref.h (r (M.proj z))) =
      Real.log ((muLine Hd).h z) - Real.log (S.ref.h z) := fun z hz =>
    log_diff_orbit S.ref_deg.symm hz.1 ((proj_eq M (hr _) hz).1 (hr' _).symm)
  have hV : ∀ z ∈ mcPts (mCoordIdeal D.y), r (M.proj z) ∉ D.Bd ↔ z ∉ D.Bd := fun z hz =>
    not_congr ⟨bd_orbit D ((proj_eq M hz (hr _)).1 (hr' _)), bd_orbit D ((proj_eq M (hr _) hz).1 (hr' _).symm)⟩
  have key : ∀ x, r x ∉ D.Bd → ∃ s : M.Xc → (Σ k, J k) → ℂ, ContinuousAt s x ∧
      ∀ᶠ y in 𝓝 x, s y ∈ D.Xo ∧ M.proj (s y) = y := by
    intro x hx
    obtain ⟨U, hU, hxU, s, hs, hs'⟩ := M.sections x
    have hc : ContinuousAt s x := continuousAt_pi.2 fun p => holo_cont (hs' p) hxU
    refine ⟨s, hc, ?_⟩
    obtain ⟨F, hF, hF'⟩ := isClosed_induced_iff.1 D.bd_closed
    have hm : ∀ z ∈ mcPts (mCoordIdeal D.y), z ∈ F ↔ z ∈ D.Bd := fun z hz => Set.ext_iff.1 hF' ⟨z, hz⟩
    have h1 : s x ∈ Fᶜ := fun h => (hV _ (hs x hxU).1).1 (by rwa [(hs x hxU).2]) ((hm _ (hs x hxU).1).1 h)
    filter_upwards [hU.mem_nhds hxU, hc.eventually_mem (hF.isOpen_compl.mem_nhds h1)] with y hy hy'
    exact ⟨⟨(hs y hy).1, fun h => hy' ((hm _ (hs y hy).1).2 h)⟩, (hs y hy).2⟩
  refine ⟨{x | r x ∉ D.Bd}, fun x => Real.log ((muLine Hd).h (r x)) - Real.log (S.ref.h (r x)), ?_, ?_, ?_,
    fun z hz => ⟨(hV z hz).2, hg z hz⟩⟩
  · refine isOpen_iff_mem_nhds.2 fun x hx => ?_
    obtain ⟨s, -, hs⟩ := key x hx
    filter_upwards [hs] with y hy
    have := (hV _ hy.1.1).2 hy.1.2
    rwa [hy.2] at this
  · intro x hx
    obtain ⟨s, hc, hs⟩ := key x hx
    have h1 := (contOn_Xo D Hd S.ref S.ref_deg.symm S.ref_smooth _ hs.self_of_nhds.1).tendsto.comp
      (tendsto_nhdsWithin_iff.2 ⟨hc.tendsto, hs.mono fun y hy => hy.1⟩)
    have h2 : ∀ y, s y ∈ D.Xo ∧ M.proj (s y) = y → Real.log ((muLine Hd).h (s y)) - Real.log (S.ref.h (s y)) =
        Real.log ((muLine Hd).h (r y)) - Real.log (S.ref.h (r y)) := fun y hy => by
      rw [← hg _ hy.1.1, hy.2]
    rw [h2 x hs.self_of_nhds] at h1
    exact ContinuousAt.continuousWithinAt (h1.congr' (hs.mono fun y hy => h2 y hy))
  · intro x hx
    have := S.ph_eq (r x) ⟨⟨hr x, hx.1⟩, hr x⟩ (by rw [hr']; exact hx.2)
    rw [hr'] at this
    exact this.symm

theorem holoMap_proj (M : XModel D) {e : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas e X) (U : X → Set X)
    (hU : ∀ x, IsOpen (U x) ∧ x ∈ U x) (lv : X → X → (Σ k, J k) → ℂ) (hl : ∀ x p, A.HoloOn (U x) fun y => lv x y p)
    (hm : ∀ x, ∀ y ∈ U x, lv x y ∈ mcPts (mCoordIdeal D.y))
    (ho : ∀ x, ∀ y ∈ U x, M.proj (lv y y) = M.proj (lv x y)) : HoloMap A M.atlas fun x => M.proj (lv x x) := by
  have hc : ∀ x, ContinuousAt (lv x) x := fun x => continuousAt_pi.2 fun p => holo_cont (hl x p) (hU x).2
  have hn : ∀ x, U x ∈ 𝓝 x := fun x => (hU x).1.mem_nhds (hU x).2
  refine ⟨continuous_iff_continuousAt.2 fun x => ?_, fun j k y hy => ?_⟩
  · have h1 := (M.cont _ (hm x x (hU x).2)).tendsto.comp
      (tendsto_nhdsWithin_iff.2 ⟨(hc x).tendsto, Filter.mem_of_superset (hn x) (hm x)⟩)
    exact h1.congr' (Filter.mem_of_superset (hn x) fun y hy => (ho x y hy).symm)
  · obtain ⟨x, hx⟩ : ∃ x, x = (A.chart j).symm y := ⟨_, rfl⟩
    obtain ⟨a, T, hT, hb, h⟩ := exists_read D (hm x x (hU x).2)
    have h0 := h.self_of_nhds (hm x x (hU x).2)
    have hp : ∀ z ∈ mcPts (mCoordIdeal D.y), T z ∈ Metric.ball 0 1 ∧ SameOrbit z ((D.chart a).γ (T z)) →
        M.proj ((D.chart a).γ (T z)) = M.proj z := fun z hz h' => (proj_eq M hz ((D.chart a).mem _ h'.1)).2 h'.2
    have h1 := (GlobalTheory.T.projection_of_chart_analytic K J II Ψ Ω W D M a k _ hb (by
      rw [hp _ (hm x x (hU x).2) h0, hx]; exact hy.2)).1
    have h2 : AnalyticAt ℂ (fun y' => lv x ((A.chart j).symm y')) y :=
      analyticAt_pi_iff.2 fun p => hl x p j y ⟨hy.1, by rw [Set.mem_preimage, ← hx]; exact (hU x).2⟩
    have h3 : AnalyticAt ℂ (T ∘ fun y' => lv x ((A.chart j).symm y')) y := AnalyticAt.comp (by rwa [← hx]) h2
    have h4 := AnalyticAt.comp (f := T ∘ fun y' => lv x ((A.chart j).symm y')) (x := y)
      (by rw [Function.comp_apply, ← hx]; exact h1) h3
    refine h4.congr ?_
    have hs : Tendsto (A.chart j).symm (𝓝 y) (𝓝 x) := hx ▸ (A.chart j).continuousAt_symm hy.1
    filter_upwards [hs.eventually (hn x), hs.eventually ((hc x).eventually h)] with y' h5 h6
    simp only [Function.comp_apply]
    rw [hp _ (hm x _ h5) (h6 (hm x _ h5)), ho x _ h5]

theorem baseSide (hU : RegUnif) : BaseSide := by
  intro K _ J _ II Ψ _ Ω _ _ W _ _ D Hd M S B K' _ J' _ P' B' e R κ v Θ Mt hS hv hP hΘ hΘp hMt
  classical
  have hpl := GlobalTheory.T.block_pullback_herm_line K J K' J' κ v hv
  let lv : R.X → R.X → (Σ k, J k) → ℂ := fun x y p => R.lift x y (v p)
  have hm : ∀ x, ∀ y ∈ R.U x, lv x y ∈ mcPts (mCoordIdeal D.y) := fun x y hy => hP ▸ hpl.2.2.1 P' _ (R.mem x y hy)
  have ho : ∀ x, ∀ y ∈ R.U x, M.proj (lv y y) = M.proj (lv x y) := by
    intro x y hy
    obtain ⟨c, hc, h⟩ := R.compat x y y ⟨hy, R.mem_U y⟩
    refine (proj_eq M (hm x y hy) (hm y y (R.mem_U y))).2 ⟨fun k => c (κ k), fun k => hc _, funext fun p => ?_⟩
    simp only [lv, h, hv.2.2.1]
  have hπ := holoMap_proj D M R.A R.U (fun x => ⟨R.isOpen_U x, R.mem_U x⟩) lv (fun x p => R.holo x _) hm ho
  set π : R.X → M.Xc := fun x => M.proj (lv x x) with hπd
  have hSB : ∀ p : D.SB B, (p : ℕ) ∈ D.S := fun p => (Finset.mem_filter.1 p.2).1
  choose Ap hAa hAs hAc hAh using fun p : D.SB B => (GlobalTheory.T.vertical_factor_smooth_hermitian_metric K J II Ψ Ω W D p (hSB p)).1
  let N₀ : HermLine J := Top.combLine (fun o : Option (D.SB B) => o.elim S.ref Ap) fun _ => 1
  have hN : IsSmoothHerm N₀ := (GlobalTheory.T.hermitian_combination_smooth_conj K J _ _ _).1 fun o => by
    cases o
    exacts [S.ref_smooth, hAs _]
  have hNa : N₀.a = muTwDeg Hd B := by
    simp only [N₀, Top.combLine, Fintype.sum_option, one_smul, Option.elim, hAa, S.ref_deg, muTwDeg]
    rw [Finset.sum_coe_sort (D.SB B) D.vdeg]
    rfl
  have hNh : ∀ z ∈ mcPts (mCoordIdeal D.y),
      Real.log (N₀.h z) = Real.log (S.ref.h z) + ∑ p ∈ D.SB B, Real.log (D.vertFactor p z) := by
    intro z hz
    simp only [N₀, Top.combLine, Fintype.prod_option, zpow_one, Option.elim]
    rw [Real.log_mul (S.ref.pos z hz.1).ne' (Finset.prod_ne_zero_iff.2 fun p _ => ((Ap p).pos z hz.1).ne'),
      Real.log_prod fun p _ => ((Ap p).pos z hz.1).ne', ← Finset.sum_coe_sort (D.SB B)]
    simp only [hAh _ z hz]
  obtain ⟨ref, href⟩ := (hpl.1 N₀).exists
  obtain ⟨V, g, hV, hg, hgS, hgz⟩ := exists_ext D Hd M S
  obtain ⟨⟨C₁, hC₁⟩, hun⟩ := hU K J _ _ M D.Xo _ S V g hS hV hg hgS
  obtain ⟨Θ', hΘ', hΘ'p, -⟩ := GlobalTheory.T.exists_positive_potential_dominating K J II Ψ Ω W D M S.R.th S.R.th_pot
  obtain ⟨-, ⟨C₂, hC₂⟩, hw⟩ := GlobalTheory.T.regularized_weight_psh_and_bounds K J _ _ M D.Xo _ S Θ' hS hΘ' hΘ'p
  obtain ⟨C₃, hC₃⟩ := exists_psh_pull hπ hΘ hΘp (pot_rsmul hΘ' 1)
  have hreg := GlobalTheory.T.regularized_hodge_metric_smooth K J II Ψ Ω W D Hd M S B hS
  have hloc : ∀ x, LocRe R.A (fun y => Real.log (N₀.h (lv x y)) - S.R.th.φ (π x) (π y)) x := by
    intro x
    obtain ⟨U, hUo, hxU, -, s, hs, hs', G, hG, hG'⟩ := S.th_ref (π x) (π x) (S.R.th.mem_U _)
    have h1 : LocRe M.atlas (fun y => S.R.th.φ (π x) y - Real.log (S.ref.h (s y))) (π x) := ⟨U, hUo, hxU, G, hG, hG'⟩
    have h2 : LocRe M.atlas (fun y => ∑ p ∈ D.SB B, Real.log (D.vertFactor p (s y))) (π x) := LocRe.sum _ fun p hp => by
      obtain ⟨V', a1, a2, -, a3⟩ := GlobalTheory.T.local_section_vertical_factor II Ψ K J Ω W D p M U s (hSB ⟨p, hp⟩) hUo (fun y hy => (hs y hy).1) hs' _ hxU
      exact ⟨V', a1, a2, a3⟩
    have hO : IsOpen (R.U x ∩ π ⁻¹' U) := (R.isOpen_U x).inter (hUo.preimage hπ.1)
    have h3 := locRe_orbit (A := R.A) N₀ hO (s := lv x) (s' := fun y => s (π y))
      (fun p => holo_mono (R.holo x _) Set.inter_subset_left) (fun p => holo_mono (holo_comp (hs' p) hπ) Set.inter_subset_right)
      (fun y hy => (hs _ hy.2).1.1)
      (fun y hy => (proj_eq M (hm x y hy.1) (hs _ hy.2).1).1 ((hs _ hy.2).2.trans (ho x y hy.1))) ⟨R.mem_U x, hxU⟩
    refine ((h3.add (h2.comp hπ)).add ((h1.comp hπ).mul (-1))).congr ?_
    filter_upwards [hO.mem_nhds ⟨R.mem_U x, hxU⟩] with y hy
    rw [hNh _ (hs _ hy.2).1]
    ring
  have hval : ∀ᶠ t in 𝓝[>] (0 : ℝ), ∀ x, ∀ y ∈ R.U x,
      Real.log ((Mt t).h (R.lift x y)) = Real.log (N₀.h (lv x y)) + S.regWeight t (π y) := by
    filter_upwards [hreg] with t ht x y hy
    rw [(hMt t).2, ht.2.2 _ (hm x y hy), hNh _ (hm x y hy), ← ho x y hy]
    ring
  have hmu : ∀ x, Real.log ((muVert Hd B).h (lv x x)) = Real.log (N₀.h (lv x x)) + g (π x) := by
    intro x
    have hx := hm x x (R.mem_U x)
    rw [GlobalTheory.T.vertical_hodge_metric_log_formula K J II Ψ Ω W D Hd B _ hx, hNh _ hx, (hgz _ hx).2]
    ring
  refine ⟨ref, max C₁ C₃, hpl.2.1 _ _ href hN, ?_, fun K₀ hK₀ hKc => ?_⟩
  · filter_upwards [hreg, hC₁, hC₂, hw 1 one_pos, hval] with t h1 h2 h3 h4 h5
    have hs := hpl.2.1 _ _ (hMt t) h1.1
    have hp := isPotential_potOf R hs
    refine ⟨hs, by rw [(hMt t).1, href.1, h1.2.1, hNa], ?_, fun x => ?_, fun x hx => ?_⟩
    · have h6 := hC₃ _ _ hp (isPotentialAdd _ _ _ S.R.th_pot (isPotential_ofFun _ _ h3.1)) h4 fun x => (hloc x).congr (by
        filter_upwards [(R.isOpen_U x).mem_nhds (R.mem_U x)] with y hy
        show Real.log ((Mt t).h (R.lift x y)) - (S.R.th.φ (π x) (π y) + S.regWeight t (π y)) = _
        rw [h5 x y hy]
        ring)
      have h7 := isPshAdd R.A _ _ (isPotentialAdd _ _ _ hp (pot_rsmul hΘ C₃)) (pot_rsmul hΘ (max C₁ C₃ - C₃)) h6
        (isPshRsmul R.A _ _ (sub_nonneg.2 (le_max_right _ _)) hΘ (TailBoundAlt.isPsh_of_isPosPot _ _ hΘp))
      refine TailBoundAlt.isPsh_congr R.A _ _ h7 (fun x y hy => ⟨hy, hy.2⟩) ?_
      funext x y
      show _ + _ * Θ.φ x y = _ + C₃ * Θ.φ x y + _ * Θ.φ x y
      ring
    · rw [h5 x x (R.mem_U x), href.2, add_sub_cancel_left]
      exact (h2.1 _).trans (le_max_left _ _)
    · rw [h5 x x (R.mem_U x), hmu]
      exact add_le_add le_rfl (h2.2 _ ((hgz _ (hm x x (R.mem_U x))).1 hx))
  · have h1 := hun (π '' K₀) (by
      rintro _ ⟨x, hx, rfl⟩
      exact (hgz _ (hm x x (R.mem_U x))).1 (hK₀ hx)) (hKc.image hπ.1)
    rw [Metric.tendstoUniformlyOn_iff] at h1 ⊢
    intro ε hε
    filter_upwards [h1 ε hε, hval] with t h2 h3 x hx
    have := h2 _ ⟨x, hx, rfl⟩
    rw [h3 x x (R.mem_U x), hmu, Real.dist_eq] at *
    rwa [show (0 : ℝ) - (Real.log (N₀.h (lv x x)) + S.regWeight t (π x) - (Real.log (N₀.h (lv x x)) + g (π x))) =
      g (π x) - S.regWeight t (π x) by ring]

end LevelTowerAlt.Comparison₂
