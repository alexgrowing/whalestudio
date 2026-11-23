import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.PotentialsBoundedRegSettingEqReference
import GroundTheory.HeightsAndTheta.Heights.Regularisation.BoundedStatements
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterSt
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PParametricCircleIntegralAnalytic
import Development.AutomorphicSpectrum.Proofs.MetricProofs.LeviChartRegularityStatementHolds

open Filter Topology Metric Set
open ReciprocityTheory.ChartRestriction.G.Geo GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar.Cusp
open ReciprocityTheory.AnForm.M (FinHolAtlas IsCompatChart)

namespace LevelTowerAlt.Charts

theorem an_of_diff {σ τ : Type} [Fintype σ] [Fintype τ] {U : Set (σ → ℂ)} {f : (σ → ℂ) → τ → ℂ} (hU : IsOpen U)
    (hf : DifferentiableOn ℂ f U) : AnalyticOnNhd ℂ f U := fun x hx => analyticAt_pi_iff.2 fun i =>
  GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.ParametricCircleIntegralAnalytic.analyticOnNhd_of_differentiableOn_fd hU
    (differentiableOn_pi.1 hf i) x hx

theorem an_star_star {σ τ : Type} [Fintype σ] [Fintype τ] {U : Set (σ → ℂ)} {f : (σ → ℂ) → τ → ℂ} (hU : IsOpen U)
    (hf : AnalyticOnNhd ℂ f U) : AnalyticOnNhd ℂ (fun t => star (f (star t))) (star ⁻¹' U) :=
  an_of_diff (hU.preimage continuous_star) fun t ht => by
    have := (hf (star t) ht).differentiableAt.star_star
    rw [star_star] at this
    exact this.differentiableWithinAt

theorem continuousAt_of_holo {n : ℕ} {X E : Type} [TopologicalSpace X] [NormedAddCommGroup E] [NormedSpace ℂ E]
    {A : FinHolAtlas n X} {U : Set X} {f : X → E}
    (hf : ∀ j, AnalyticOnNhd ℂ (f ∘ (A.chart j).symm) ((A.chart j).target ∩ (A.chart j).symm ⁻¹' U))
    {x : X} (hx : x ∈ U) : ContinuousAt f x := by
  obtain ⟨j, hj⟩ := A.cover x
  have h1 := (hf j (A.chart j x) ⟨(A.chart j).map_source hj, by simp [(A.chart j).left_inv hj, hx]⟩).continuousAt
  refine (h1.comp ((A.chart j).continuousAt hj)).congr ?_
  filter_upwards [(A.chart j).open_source.mem_nhds hj] with y hy
  simp [(A.chart j).left_inv hy]

section Good

variable {K : Type} [Fintype K] {J : K → Type} [∀ k, Fintype (J k)] {n : ℕ}

structure Good (P : Ideal (MRing J)) (γ : (Fin n → ℂ) → (Σ k, J k) → ℂ) : Prop where
  an : AnalyticOnNhd ℂ γ (ball 0 1)
  mem : ∀ t ∈ ball (0 : Fin n → ℂ) 1, γ t ∈ mcPts P
  inj : ∀ t ∈ ball (0 : Fin n → ℂ) 1, ∀ t' ∈ ball (0 : Fin n → ℂ) 1,
    ∀ c : K → ℂ, (∀ k, c k ≠ 0) → γ t = torusSmul c (γ t') → t = t'
  loc : ∀ t₀ ∈ ball (0 : Fin n → ℂ) 1, ∃ (V : Set ((Σ k, J k) → ℂ)) (T : ((Σ k, J k) → ℂ) → Fin n → ℂ),
    IsOpen V ∧ γ t₀ ∈ V ∧ AnalyticOnNhd ℂ T V ∧ T (γ t₀) = t₀ ∧
      ∀ z ∈ V ∩ mcPts P, T z ∈ ball 0 1 ∧ ∃ c : K → ℂ, (∀ k, c k ≠ 0) ∧ z = torusSmul c (γ (T z))

variable {P : Ideal (MRing J)} {γ : (Fin n → ℂ) → (Σ k, J k) → ℂ}

theorem Good.affine (h : Good P γ) {t₀ : Fin n → ℂ} {ε : ℝ} (h₀ : ‖t₀‖ ≤ 1 / 2) (hε : 0 < ε) (hε' : ε ≤ 1 / 4) :
    Good P fun t => γ (t₀ + (ε : ℂ) • t) := by
  have hb : ∀ t ∈ ball (0 : Fin n → ℂ) 1, t₀ + (ε : ℂ) • t ∈ ball (0 : Fin n → ℂ) 1 := fun t ht =>
    SncPiece.add_smul_mem_ball h₀ hε hε' ((mem_ball_zero_iff.1 ht).trans one_lt_two)
  have hne : (ε : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hε.ne'
  refine ⟨fun t ht => (h.an _ (hb t ht)).comp_of_eq
      (analyticAt_const.add (analyticAt_id.const_smul (c := (ε : ℂ)))) rfl, fun t ht => h.mem _ (hb t ht),
    fun t ht t' ht' c hc e => smul_right_injective _ hne (add_left_cancel (h.inj _ (hb t ht) _ (hb t' ht') c hc e)),
    fun s hs => ?_⟩
  obtain ⟨V, T, hV, hm, hT, hTe, hz⟩ := h.loc _ (hb s hs)
  refine ⟨V ∩ T ⁻¹' ball t₀ ε, fun z => (ε : ℂ)⁻¹ • (T z - t₀),
    hT.continuousOn.isOpen_inter_preimage hV isOpen_ball, ⟨hm, ?_⟩,
    fun z hz => ((hT z hz.1).sub (analyticAt_const (v := t₀))).const_smul (c := (ε : ℂ)⁻¹), ?_, fun z hz' => ⟨?_, ?_⟩⟩
  · rw [mem_preimage, hTe, mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul, Complex.norm_real,
      Real.norm_of_nonneg hε.le]
    exact mul_lt_of_lt_one_right hε (mem_ball_zero_iff.1 hs)
  · simp only [hTe, add_sub_cancel_left, inv_smul_smul₀ hne]
  · have h1 : ‖T z - t₀‖ < ε := by simpa [dist_eq_norm] using hz'.1.2
    rw [mem_ball_zero_iff, norm_smul, norm_inv, Complex.norm_real, Real.norm_of_nonneg hε.le,
      inv_mul_lt_iff₀ hε, mul_one]
    exact h1
  · simp only [smul_inv_smul₀ hne, add_sub_cancel]
    exact (hz z ⟨hz'.1.1, hz'.2⟩).2

def cj (γ : (Fin n → ℂ) → (Σ k, J k) → ℂ) : (Fin n → ℂ) → (Σ k, J k) → ℂ := fun t => conjVec (γ (star t))

omit [Fintype K] [∀ k, Fintype (J k)] in
theorem cj_cj (γ : (Fin n → ℂ) → (Σ k, J k) → ℂ) : cj (cj γ) = γ := by
  funext t
  simp only [cj, star_star, SncPiece.conj_conj]

omit [Fintype K] [∀ k, Fintype (J k)] in
theorem conj_torus (c : K → ℂ) (z : (Σ k, J k) → ℂ) :
    conjVec (torusSmul c z) = torusSmul (fun k => starRingEnd ℂ (c k)) (conjVec z) := by
  funext p
  simp [conjVec, torusSmul]

theorem star_mem_ball {t : Fin n → ℂ} {r : ℝ} : star t ∈ ball (0 : Fin n → ℂ) r ↔ t ∈ ball (0 : Fin n → ℂ) r := by
  simp only [mem_ball_zero_iff, norm_star]

theorem Good.cj (h : Good P γ) : Good P (cj γ) := by
  refine ⟨fun t ht => an_star_star isOpen_ball h.an t (star_mem_ball.2 ht),
    fun t ht => SncPiece.conj_mem (h.mem _ (star_mem_ball.2 ht)), fun t ht t' ht' c hc e => ?_, fun s hs => ?_⟩
  · have e' := congrArg conjVec e
    simp only [Charts.cj, conj_torus, SncPiece.conj_conj] at e'
    exact star_injective (h.inj _ (star_mem_ball.2 ht) _ (star_mem_ball.2 ht') _
      (fun k => (map_ne_zero _).2 (hc k)) e')
  · obtain ⟨V, T, hV, hm, hT, hTe, hz⟩ := h.loc _ (star_mem_ball.2 hs)
    have hcc : star (Charts.cj γ s) = γ (star s) := SncPiece.conj_conj _
    refine ⟨star ⁻¹' V, fun z => star (T (star z)), hV.preimage continuous_star, by rwa [mem_preimage, hcc],
      an_star_star hV hT, by simp only [hcc, hTe, star_star], fun z hz' => ?_⟩
    obtain ⟨h1, c, hc, e⟩ := hz (conjVec z) ⟨hz'.1, SncPiece.conj_mem hz'.2⟩
    refine ⟨star_mem_ball.2 h1, fun k => starRingEnd ℂ (c k), fun k => (map_ne_zero _).2 (hc k), ?_⟩
    have e' := congrArg conjVec e
    rw [SncPiece.conj_conj, conj_torus] at e'
    simp only [Charts.cj, star_star]
    exact e'

theorem sec_diff (M : CxModel P n) (L : HermLine J) {U U' : Set M.Xc} (hU : IsOpen U) (hU' : IsOpen U')
    {s s' : M.Xc → (Σ k, J k) → ℂ} (hs : ∀ y ∈ U, s y ∈ mcPts P ∧ M.proj (s y) = y)
    (hs' : ∀ y ∈ U', s' y ∈ mcPts P ∧ M.proj (s' y) = y) (hh : ∀ p, M.atlas.HoloOn U fun y => s y p)
    (hh' : ∀ p, M.atlas.HoloOn U' fun y => s' y p) {y : M.Xc} (hy' : y ∈ U ∩ U') :
    ∃ W : Set M.Xc, IsOpen W ∧ y ∈ W ∧ ∃ G : M.Xc → ℂ, M.atlas.HoloOn W G ∧
      ∀ z ∈ W ∩ U ∩ U', Real.log (L.h (s z)) - Real.log (L.h (s' z)) = (G z).re := by
  classical
  have ext : ∀ z ∈ U ∩ U', ∃ t : K → ℂ, (∀ k, t k ≠ 0) ∧ s z = fun q => t q.1 * s' z q := fun z hz =>
    (M.fibre _ (hs' z hz.2).1 _ (hs z hz.1).1).mp ((hs' z hz.2).2.trans (hs z hz.1).2.symm)
  choose p hp using (hs' y hy'.2).1.1
  obtain ⟨c, hc, hcy⟩ := ext y hy'
  have hnum : ∀ k, s y ⟨k, p k⟩ ≠ 0 := fun k => by
    rw [hcy]; exact mul_ne_zero (hc k) (hp k)
  have hr : ∀ k, s y ⟨k, p k⟩ / s' y ⟨k, p k⟩ ≠ 0 := fun k => div_ne_zero (hnum k) (hp k)
  have hO : IsOpen (U ∩ U') := hU.inter hU'
  let q : K → M.Xc → ℂ := fun k z => s z ⟨k, p k⟩ / s' z ⟨k, p k⟩ / (s y ⟨k, p k⟩ / s' y ⟨k, p k⟩)
  let W : Set M.Xc := {z | z ∈ U ∩ U' ∧ ∀ k, s' z ⟨k, p k⟩ ≠ 0 ∧ q k z ∈ Complex.slitPlane}
  have hW : IsOpen W := by
    refine isOpen_iff_mem_nhds.mpr fun z hz => ?_
    have hn : ∀ k, ContinuousAt (fun z => s z ⟨k, p k⟩) z := fun k => continuousAt_of_holo (hh _) hz.1.1
    have hd : ∀ k, ContinuousAt (fun z => s' z ⟨k, p k⟩) z := fun k => continuousAt_of_holo (hh' _) hz.1.2
    filter_upwards [hO.mem_nhds hz.1, eventually_all.mpr fun k => (hd k).eventually_ne (hz.2 k).1,
      eventually_all.mpr fun k => (((hn k).div (hd k) (hz.2 k).1).div_const _).eventually_mem
        (Complex.isOpen_slitPlane.mem_nhds (hz.2 k).2)] with w h1 h2 h3
    exact ⟨h1, fun k => ⟨h2 k, h3 k⟩⟩
  have hyW : y ∈ W := by
    refine ⟨hy', fun k => ⟨hp k, ?_⟩⟩
    have : q k y = 1 := div_self (hr k)
    rw [this]
    exact Complex.mem_slitPlane_iff.mpr (Or.inl (by simp))
  let G : M.Xc → ℂ := fun z => ∑ k, ((L.a k : ℝ) : ℂ) *
    (Complex.log (q k z) + ((Real.log ‖s y ⟨k, p k⟩ / s' y ⟨k, p k⟩‖ : ℝ) : ℂ))
  refine ⟨W, hW, hyW, G, fun j y' hy'' => ?_, fun z hz => ?_⟩
  · have hz : (M.atlas.chart j).symm y' ∈ W := hy''.2
    have hterm : ∀ k, AnalyticAt ℂ (fun y'' => ((L.a k : ℝ) : ℂ) *
        (Complex.log (q k ((M.atlas.chart j).symm y'')) +
          ((Real.log ‖s y ⟨k, p k⟩ / s' y ⟨k, p k⟩‖ : ℝ) : ℂ))) y' := by
      intro k
      have hn : AnalyticAt ℂ (fun y'' => s ((M.atlas.chart j).symm y'') ⟨k, p k⟩) y' :=
        hh _ j y' ⟨hy''.1, hz.1.1⟩
      have hd : AnalyticAt ℂ (fun y'' => s' ((M.atlas.chart j).symm y'') ⟨k, p k⟩) y' :=
        hh' _ j y' ⟨hy''.1, hz.1.2⟩
      have hq : AnalyticAt ℂ (fun y'' => q k ((M.atlas.chart j).symm y'')) y' :=
        (hn.div hd (hz.2 k).1).div analyticAt_const (hr k)
      have hl : AnalyticAt ℂ (Complex.log ∘ fun y'' => q k ((M.atlas.chart j).symm y'')) y' :=
        AnalyticAt.comp (f := fun y'' => q k ((M.atlas.chart j).symm y''))
          (analyticAt_clog (hz.2 k).2) hq
      exact analyticAt_const.mul (hl.add analyticAt_const)
    exact Finset.analyticAt_fun_sum _ fun k _ => hterm k
  · have hzW : z ∈ W := hz.1.1
    obtain ⟨c', hc', hcz⟩ := ext z hzW.1
    have hpos : 0 < L.h (s' z) := L.pos _ (hs' z hzW.1.2).1.1
    have hprod : (∏ k, ‖c' k‖ ^ L.a k) ≠ 0 :=
      Finset.prod_ne_zero_iff.mpr fun k _ => zpow_ne_zero _ (norm_ne_zero_iff.mpr (hc' k))
    have hterm : ∀ k, Real.log ‖q k z‖ + Real.log ‖s y ⟨k, p k⟩ / s' y ⟨k, p k⟩‖ = Real.log ‖c' k‖ := by
      intro k
      have hqz : q k z = c' k / (s y ⟨k, p k⟩ / s' y ⟨k, p k⟩) := by
        simp only [q]
        rw [hcz, mul_div_assoc, div_self (hzW.2 k).1, mul_one]
      rw [hqz, norm_div, Real.log_div (norm_ne_zero_iff.mpr (hc' k)) (norm_ne_zero_iff.mpr (hr k))]
      ring
    rw [hcz, L.smul c' _ hc', Real.log_mul hprod hpos.ne', add_sub_cancel_right,
      Real.log_prod fun k _ => zpow_ne_zero _ (norm_ne_zero_iff.mpr (hc' k))]
    simp only [G, Complex.re_sum, Complex.re_ofReal_mul, Complex.add_re, Complex.log_re, Complex.ofReal_re]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hterm k, Real.log_zpow]

end Good

variable {K : Type} [Fintype K] {J : K → Type} [∀ k, Fintype (J k)] {II : IntersectionSystem} {Ψ : Type} [Fintype Ψ]
  {Ω : Type} [Field Ω] [Algebra ℚ Ω] {W : Ψ → Type} [∀ τ, AddCommGroup (W τ)] [∀ τ, Module Ω (W τ)]
  {D : ComponentData II Ψ K J Ω W} (M : XModel D) {γ : (Fin D.n → ℂ) → (Σ k, J k) → ℂ}

theorem Good.locInv (h : Good (mCoordIdeal D.y) γ) {t₀ : Fin D.n → ℂ} (ht : t₀ ∈ ball (0 : Fin D.n → ℂ) 1) :
    ∃ U : Set M.Xc, IsOpen U ∧ M.proj (γ t₀) ∈ U ∧ ∃ ψ : M.Xc → Fin D.n → ℂ,
      (∀ j, AnalyticOnNhd ℂ (ψ ∘ (M.atlas.chart j).symm)
        ((M.atlas.chart j).target ∩ (M.atlas.chart j).symm ⁻¹' U)) ∧
      ∀ x ∈ U, ψ x ∈ ball (0 : Fin D.n → ℂ) 1 ∧ M.proj (γ (ψ x)) = x := by
  obtain ⟨V, T, hV, hm, hT, -, hz⟩ := h.loc t₀ ht
  obtain ⟨U, hU, hx, s, hs, hh⟩ := M.sections (M.proj (γ t₀))
  obtain ⟨c, hc, e⟩ := (M.fibre _ (hs _ hx).1 _ (h.mem _ ht)).1 (hs _ hx).2
  have hs' : ∀ j, AnalyticOnNhd ℂ ((fun x => torusSmul c (s x)) ∘ (M.atlas.chart j).symm)
      ((M.atlas.chart j).target ∩ (M.atlas.chart j).symm ⁻¹' U) := fun j y hy =>
    analyticAt_pi_iff.2 fun p => analyticAt_const.mul (hh p j y hy)
  have hmem : ∀ x ∈ U, torusSmul c (s x) ∈ mcPts (mCoordIdeal D.y) := fun x hx =>
    mcPts_smul D.arith.2.1.2.1 c hc (hs x hx).1
  refine ⟨U ∩ (fun x => torusSmul c (s x)) ⁻¹' V, ContinuousOn.isOpen_inter_preimage
    (fun x hx => (continuousAt_of_holo hs' hx).continuousWithinAt) hU hV, ⟨hx, by rw [mem_preimage, ← e]; exact hm⟩,
    fun x => T (torusSmul c (s x)), fun j y hy => (hT _ hy.2.2).comp_of_eq (hs' j y ⟨hy.1, hy.2.1⟩) rfl,
    fun x hx => ?_⟩
  obtain ⟨h1, c', hc', e'⟩ := hz _ ⟨hx.2, hmem x hx.1⟩
  refine ⟨h1, ?_⟩
  rw [(M.fibre _ (h.mem _ h1) _ (hmem x hx.1)).2 ⟨c', hc', e'⟩,
    ← (M.fibre _ (hs x hx.1).1 _ (hmem x hx.1)).2 ⟨c, hc, rfl⟩, (hs x hx.1).2]

theorem Good.exists_chart (h : Good (mCoordIdeal D.y) γ) :
    ∃ e : OpenPartialHomeomorph M.Xc (Fin D.n → ℂ), e.target = ball 0 1 ∧ (∀ t, e.symm t = M.proj (γ t)) ∧
      IsCompatChart M.atlas e := by
  let g : (Fin D.n → ℂ) → M.Xc := fun t => M.proj (γ t)
  have hinj : InjOn g (ball 0 1) := fun t ht t' ht' e => by
    obtain ⟨c, hc, e'⟩ := (M.fibre _ (h.mem _ ht') _ (h.mem _ ht)).1 e.symm
    exact h.inj t ht t' ht' c hc e'
  have hloc : ∀ x ∈ g '' ball 0 1, ∃ U : Set M.Xc, IsOpen U ∧ x ∈ U ∧ U ⊆ g '' ball 0 1 ∧
      ∀ j, AnalyticOnNhd ℂ (Function.invFunOn g (ball 0 1) ∘ (M.atlas.chart j).symm)
        ((M.atlas.chart j).target ∩ (M.atlas.chart j).symm ⁻¹' U) := by
    rintro _ ⟨t, ht, rfl⟩
    obtain ⟨U, hU, hx, ψ, hψ, hi⟩ := h.locInv M ht
    refine ⟨U, hU, hx, fun x hx => ⟨ψ x, hi x hx⟩, fun j => ?_⟩
    refine (hψ j).congr ((M.atlas.chart j).isOpen_inter_preimage_symm hU) fun y hy => ?_
    have h1 := hi _ hy.2
    have h2 := hinj.leftInvOn_invFunOn h1.1
    simp only [g, h1.2] at h2
    exact h2.symm
  have hall : ∀ j, AnalyticOnNhd ℂ (Function.invFunOn g (ball 0 1) ∘ (M.atlas.chart j).symm)
      ((M.atlas.chart j).target ∩ (M.atlas.chart j).symm ⁻¹' (g '' ball 0 1)) := fun j y hy => by
    obtain ⟨U, -, hx, -, ha⟩ := hloc _ hy.2
    exact ha j y ⟨hy.1, hx⟩
  refine ⟨{ toPartialEquiv := (hinj.toPartialEquiv g (ball 0 1)).symm
            open_source := ?_
            open_target := isOpen_ball
            continuousOn_toFun := fun x hx => (continuousAt_of_holo hall hx).continuousWithinAt
            continuousOn_invFun := M.cont.comp h.an.continuousOn h.mem }, rfl, fun _ => rfl,
    fun j => ⟨hall j, fun t ht => ?_⟩⟩
  · refine isOpen_iff_mem_nhds.2 fun x hx => ?_
    obtain ⟨U, hU, hxU, hsub, -⟩ := hloc x hx
    exact mem_of_superset (hU.mem_nhds hxU) hsub
  · have ht1 : t ∈ ball (0 : Fin D.n → ℂ) 1 := ht.1
    obtain ⟨V, hV, hz, F, hF, hFe⟩ := GlobalTheory.CompanionTheory.Ar.Giv.projHoloLocal II Ψ K J Ω W D M (M.atlas.chart j)
      (fun k => ⟨M.atlas.holo k j, M.atlas.holo j k⟩) (γ t) (h.mem t ht1) ht.2
    refine (((an_of_diff hV hF) _ hz).comp (h.an t ht1)).congr ?_
    filter_upwards [isOpen_ball.mem_nhds ht1, (h.an t ht1).continuousAt.preimage_mem_nhds (hV.mem_nhds hz)]
      with t' h1 h2
    exact ((hFe _ ⟨h2, h.mem t' h1⟩).2).symm

end LevelTowerAlt.Charts
