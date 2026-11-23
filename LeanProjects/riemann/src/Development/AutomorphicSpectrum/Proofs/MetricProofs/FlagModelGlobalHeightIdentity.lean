import Mathlib
import Development.AutomorphicSpectrum.Statements.TowerExistence.GoodTowerExistsX
import Development.AutomorphicSpectrum.Statements.MetricStatements.ExistsFlagModelBaseMetric
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.RootOnFund
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ContDiffUncentre
import Development.AutomorphicSpectrum.Proofs.MetricProofs.OmHeightslockG
import Development.AutomorphicSpectrum.Proofs.MetricProofs.ExistsIsFramePeriodsNoGlobal
import Development.WeilBound.CoreStatements.PluriharmonicCharts.XCBmExistsLocal
open AlgebraicGeometry CategoryTheory NumberField Matrix ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.BMx ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P
open ReciprocityTheory.ChartRestriction.G.Semi
open scoped ComplexOrder

set_option maxHeartbeats 1000000 in
open PositivityTheory.Xgp.c_bm_exists_local GroundTheory.Heights₂.Heights.LowerBoundFree in

theorem GlobalTheory.CompanionTheory.Ar.PB.BMx.exists_gram_logBounds_noGlobal : Given → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (Xo : ∀ l : Level H, Moduli D l) (l : Level H) (c : Coeff l) (Y : Model (Xo l) c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (M : FlagModel y (CMType H) (D.p + D.q) D.p) (𝔐 : HodgeCpt Y S M.x) (tie : FlagTie M 𝔐), ∀ (n : ℕ) (Rb : AnLogRes (mCoordIdeal M.x) ⊤ n) (L : LocPot Rb.X) (s : Rb.X → Rb.X → ℂ) (Bat : FinHolAtlas n Rb.X), IsPotential Rb.A L → IsSection Rb.A L s → (∀ p, logNormSec L s p ≤ 0) → IsAdaptedAtlas Rb.A Bat L s → (∀ (x : Rb.X) (z : Spec (CommRingCat.of ℂ) ⟶ 𝔐.X), CoordsAt 𝔐.ξ M.x z (Rb.lift x x) → (x ∉ bdry s ↔ 𝔐.Interior z)) → ∀ (F : FrameData ι (CMType H) (D.p + D.q) M.Ω M.blk), M.IsFrame F → ∀ (τ : CMType H) (k : Fin Bat.n) (w₀ : Fin n → ℂ), w₀ ∈ Metric.closedBall (0 : Fin n → ℂ) (3 / 2) → M.GoodAt F (mCoordIdeal (Rb.lift ((Bat.chart k).symm w₀) ((Bat.chart k).symm w₀))) → ∃ ε c C : ℝ, 0 < ε ∧ 0 < c ∧ 0 < C ∧ ∀ w : Fin n → ℂ, ‖w - w₀‖ < ε → (Bat.chart k).symm w ∉ bdry s → (baseGram tie F τ Rb ((Bat.chart k).symm w)).PosDef ∧ ((baseGram tie F τ Rb ((Bat.chart k).symm w))⁻¹ - (c : ℂ) • (1 : Matrix (Fin (D.p + D.q)) (Fin (D.p + D.q)) ℂ)).PosSemidef ∧ (((C * rW L s ((Bat.chart k).symm w) : ℝ) : ℂ) • (1 : Matrix (Fin (D.p + D.q)) (Fin (D.p + D.q)) ℂ) - (baseGram tie F τ Rb ((Bat.chart k).symm w))⁻¹).PosSemidef ∧ ∀ a b, ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun w' => baseGram tie F τ Rb ((Bat.chart k).symm w') a b) w ∧ ‖fderiv ℝ (fun w' => baseGram tie F τ Rb ((Bat.chart k).symm w') a b) w‖ ≤ C * Real.exp (rW L s ((Bat.chart k).symm w) / 2) := by
  intro _ E _ _ _ H D Xo l c Y S K _ ι _ Φ _ y M 𝔐 tie n Rb L s Bat _ _ hnorm hAd hInt F hF τ k w₀ hw₀ hgood
  classical
  obtain ⟨hAB, hball, -, M₀, hM⟩ := hAd
  obtain ⟨S₀, m, hm, hS, hr⟩ := hM k
  have tp := GlobalTheory.T.local_ring_points_existsUnique 𝔐.X M.Ω 𝔐.ξ _ _ M.x 𝔐.tie ℂ
  have uniq : ∀ {z z' : Spec (CommRingCat.of ℂ) ⟶ 𝔐.X} {w}, CoordsAt 𝔐.ξ M.x z w → CoordsAt 𝔐.ξ M.x z' w → z = z' :=
    fun {z z' w} h h' => (tp.1 w h.1 (tp.2.2 z w (𝔐.all _) h).1).unique ⟨𝔐.all _, h⟩ ⟨𝔐.all _, h'⟩
  have orb : ∀ {z : Spec (CommRingCat.of ℂ) ⟶ 𝔐.X} {w w'}, CoordsAt 𝔐.ξ M.x z w → SameOrbit w' w →
      CoordsAt 𝔐.ξ M.x z w' := fun {z w w'} h ⟨a, ha, e⟩ =>
    ((tp.2.2 z w (𝔐.all _) h).2 _).2 ⟨fun k => Units.mk0 (a k) (ha k), e⟩
  have pts : ∀ w ∈ mcPts (mCoordIdeal M.x), ∃ z : Spec (CommRingCat.of ℂ) ⟶ 𝔐.X, CoordsAt 𝔐.ξ M.x z w := fun w hw => by
    obtain ⟨z, -, hz⟩ := (GlobalTheory.T.complex_points_iff_centres 𝔐.X M.Ω 𝔐.ξ _ _ M.x 𝔐.tie w).1 hw
    exact ⟨z, hz⟩
  have gfn : ∀ (z : Spec (CommRingCat.of ℂ) ⟶ 𝔐.X) w Γ, CoordsAt 𝔐.ξ M.x z w → 𝔐.Interior z →
      𝔐.M.GramAt 𝔐.t.PP.L z (gb tie F τ) Γ → HodgeMetric.gramFn 𝔐 (gb tie F τ) w = Γ := by
    intro z w Γ hw hi hΓ
    have hex : ∃ (Γ : Matrix (Fin (D.p + D.q)) (Fin (D.p + D.q)) ℂ) (z : Spec (CommRingCat.of ℂ) ⟶ 𝔐.X),
        CoordsAt 𝔐.ξ M.x z w ∧ 𝔐.Interior z ∧ 𝔐.M.GramAt 𝔐.t.PP.L z (gb tie F τ) Γ := ⟨Γ, z, hw, hi, hΓ⟩
    unfold HodgeMetric.gramFn
    rw [dif_pos hex]
    obtain ⟨z₀, hw₀, hi₀, hΓ₀⟩ := hex.choose_spec
    rw [uniq hw₀ hw] at hΓ₀
    exact GlobalTheory.T.gram_matrix_change_frame E H D l (Xo l) c Y S M.Ω _ _ M.x 𝔐 z _ _ _ _
      (GlobalTheory.T.interior_point_polarised E H D l (Xo l) c Y S M.Ω _ _ M.x 𝔐 z hi) hΓ₀ hΓ
  let Bd : Set ((Σ k, baseIdx ι M.blk k) → ℂ) :=
    {w | ∀ z : Spec (CommRingCat.of ℂ) ⟶ 𝔐.X, CoordsAt 𝔐.ξ M.x z w → ¬ 𝔐.Interior z}
  have hBd : ∀ (z : Spec (CommRingCat.of ℂ) ⟶ 𝔐.X) w, CoordsAt 𝔐.ξ M.x z w → (w ∈ Bd ↔ ¬ 𝔐.Interior z) :=
    fun z w hz => ⟨fun h => h z hz, fun h z' hz' => uniq hz hz' ▸ h⟩
  have hZ : ∀ x₀, ∀ x ∈ Rb.U x₀, Rb.lift x₀ x ∈ Bd ↔ x ∈ bdry s := by
    intro x₀ x hx
    obtain ⟨z, hz⟩ := pts _ (Rb.mem x₀ x hx)
    rw [hBd z _ hz, ← hInt x z (orb hz (Rb.compat x x₀ x ⟨Rb.mem_U x, hx⟩)), not_not]
  have hw₀' : ‖w₀‖ ≤ 3 / 2 := mem_closedBall_zero_iff.1 hw₀
  have hw₀t : w₀ ∈ (Bat.chart k).target := hball k (mem_closedBall_zero_iff.2 (by linarith))
  obtain ⟨ρ, π, χ, hρ, hρ', hU, hγ, ha⟩ := exists_sncChart Rb Bat hAB k w₀ hw₀t Bd (bdry s) S₀ hS hZ
  have hγ0 : χ.γ 0 = Rb.lift ((Bat.chart k).symm w₀) ((Bat.chart k).symm w₀) := by
    rw [hγ, HodgeMetric.recentre_zero]
  obtain ⟨z₀, hz₀⟩ := pts _ (Rb.mem _ _ (Rb.mem_U ((Bat.chart k).symm w₀)))
  obtain ⟨f, hf, hfg⟩ := exists_goodDomain M F 𝔐.tie (𝔐.all _) hz₀ hgood
  obtain ⟨a₀, g, Λ, _, LP, π', ρ', U, hP⟩ := exists_isFramePeriods_noGlobal E H D Xo l c Y S M.Ω _ _ M.x 𝔐 (.inl τ) (.inr τ) _
    (gbS tie F τ) n Bd χ 0 F.c f hBd (Metric.mem_ball_self one_pos)
    (fun p h1 h2 => PositivityTheory.Xgp.isFrameAt_comap_gbS E H D Xo l c Y S K ι Φ y M 𝔐 tie F hF τ p (hfg p h1 h2))
    (hγ0 ▸ hf)
  obtain ⟨ε, c₀, C, hε, hερ, hc₀, hC, hb⟩ := GlobalTheory.T.period_gram_comparison_bound n a₀ g _ χ.a Λ LP U 0 π' ρ' hP.1 hP.2.1 hP.2.2.1
    hP.2.2.2.1 hP.2.2.2.2.1
  obtain ⟨A, hA⟩ := exists_hasFDerivAt_uncentre w₀ ρ π
  have hcu : Continuous (HodgeMetric.uncentre w₀ ρ π) := (HodgeMetric.contDiff_uncentre w₀ ρ π).continuous
  have hcu' : Continuous (HodgeMetric.uncentre 0 ρ' π') := (HodgeMetric.contDiff_uncentre 0 ρ' π').continuous

  have pg : ∀ w ∈ Metric.ball w₀ ρ, HodgeMetric.uncentre 0 ρ' π' (HodgeMetric.uncentre w₀ ρ π w) ∈ Flat.punct n a₀ 1 →
      baseGram tie F τ Rb ((Bat.chart k).symm w) =
        HodgeMetric.periodGram LP U (HodgeMetric.uncentre 0 ρ' π' (HodgeMetric.uncentre w₀ ρ π w)) := by
    intro w hw hu
    obtain ⟨hb1, -, hbd, hg⟩ := hP.2.2.2.2.2 _ hu.1
    rw [HodgeMetric.recentre_uncentre 0 hP.1, hγ, HodgeMetric.recentre_uncentre w₀ hρ] at hbd hg
    obtain ⟨z, hz⟩ := pts _ (Rb.mem _ _ (hU w hw).2)
    have hi : 𝔐.Interior z := by_contra fun h => hbd.2 hu ((hBd z _ hz).2 h)
    exact gfn z _ _ (orb hz (Rb.compat _ _ _ ⟨Rb.mem_U _, (hU w hw).2⟩)) hi (hg hu z hz)
  have h0 : ∀ᶠ w in nhds w₀, ‖HodgeMetric.uncentre w₀ ρ π w - 0‖ < ε := by
    have : ContinuousAt (fun w => ‖HodgeMetric.uncentre w₀ ρ π w - 0‖) w₀ := by fun_prop
    refine this.eventually_lt continuousAt_const ?_
    simpa [HodgeMetric.uncentre_self] using hε
  obtain ⟨ε₁, hε₁, hb₁⟩ := Metric.eventually_nhds_iff_ball.1 h0
  refine ⟨min ε₁ ρ, c₀, C * (1 + |M₀|) + C * Real.exp (|M₀| / 2) * ‖A‖, lt_min hε₁ hρ, hc₀, by positivity,
    fun w hw hwb => ?_⟩
  have hwρ : ‖w - w₀‖ < ρ := hw.trans_le (min_le_right _ _)
  have hwB : w ∈ Metric.ball w₀ ρ := mem_ball_iff_norm.2 hwρ
  have ht := hb₁ w (mem_ball_iff_norm.2 (hw.trans_le (min_le_left _ _)))
  have ht1 := HodgeMetric.uncentre_mem_ball hρ π hwρ
  have hub := HodgeMetric.uncentre_mem_ball hP.1 π' (ht.trans_le hερ)
  have hu : HodgeMetric.uncentre 0 ρ' π' (HodgeMetric.uncentre w₀ ρ π w) ∈ Flat.punct n a₀ 1 := by
    have hcl := (hP.2.2.2.2.2 _ hub).2.2.1
    rw [HodgeMetric.recentre_uncentre 0 hP.1, hγ, HodgeMetric.recentre_uncentre w₀ hρ, hZ _ _ (hU w hwB).2] at hcl
    exact hcl.1 hwb
  obtain ⟨b1, b2, b3⟩ := hb _ ht (mem_ball_zero_iff.1 ht1) hu
  have hev : ∀ᶠ w' in nhds w, baseGram tie F τ Rb ((Bat.chart k).symm w') =
      HodgeMetric.periodGram LP U (HodgeMetric.uncentre 0 ρ' π' (HodgeMetric.uncentre w₀ ρ π w')) := by
    filter_upwards [Metric.isOpen_ball.mem_nhds hwB,
      (hcu'.comp hcu).continuousAt.eventually ((HodgeMetric.isOpen_punct n a₀ 1).mem_nhds hu)] with w' h1 h2
    exact pg w' h1 h2
  have hw2 : ‖w‖ ≤ 2 := by
    have := norm_add_le (w - w₀) w₀
    rw [sub_add_cancel] at this
    linarith
  have hlog := logR_le hρ (by linarith) hm hw2
    (fun i hi h => hwb ((hS w (hU w hwB).1).2 ⟨i, hi, h⟩)) ha
  have hrM := abs_le.1 ((hr w (mem_closedBall_zero_iff.2 hw2) hwb).trans (le_abs_self M₀))
  have hre : 1 ≤ rW L s ((Bat.chart k).symm w) := by
    have := hnorm ((Bat.chart k).symm w)
    have h2 := Real.add_one_le_exp (1 : ℝ)
    unfold rW
    linarith
  generalize (Real.exp 1 + ∑ i : Fin n, if (i : ℕ) < χ.a then
    Real.log (1 / ‖HodgeMetric.uncentre w₀ ρ π w i‖ ^ 2) else 0) = R at b2 b3 hlog
  generalize rW L s ((Bat.chart k).symm w) = r at hrM hre ⊢
  have hR : R ≤ r + |M₀| := by linarith [hrM.1]
  have hM0 := abs_nonneg M₀
  have hX : 0 ≤ C * Real.exp (|M₀| / 2) * ‖A‖ := by positivity
  rw [hev.self_of_nhds]
  refine ⟨posDef_of_inv hc₀ b1, b1, psd_mono ?_ b2, fun a b => ?_⟩
  · have h1 : R ≤ (1 + |M₀|) * r := by nlinarith
    have h2 := mul_le_mul_of_nonneg_left h1 hC.le
    nlinarith
  · have h1 : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun t => HodgeMetric.periodGram LP U (HodgeMetric.uncentre 0 ρ' π' t) a b) (HodgeMetric.uncentre w₀ ρ π w) :=
      (GlobalTheory.T.period_gram_smooth_punctured n a₀ g _ Λ LP U hP.2.2.1 a b _ hu).comp _ (HodgeMetric.contDiff_uncentre 0 ρ' π').contDiffAt
    have h2 : (fun w' => baseGram tie F τ Rb ((Bat.chart k).symm w') a b) =ᶠ[nhds w]
        (fun t => HodgeMetric.periodGram LP U (HodgeMetric.uncentre 0 ρ' π' t) a b) ∘ HodgeMetric.uncentre w₀ ρ π := by
      filter_upwards [hev] with w' hw'
      rw [hw']
      rfl
    refine ⟨(h1.comp w (HodgeMetric.contDiff_uncentre w₀ ρ π).contDiffAt).congr_of_eventuallyEq h2, ?_⟩
    rw [h2.fderiv_eq, fderiv_comp w (h1.differentiableAt (by simp)) (hA w).differentiableAt, (hA w).fderiv]
    refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
    have h3 : Real.exp (R / 2) ≤ Real.exp (|M₀| / 2) * Real.exp (r / 2) := by
      rw [← Real.exp_add]
      exact Real.exp_le_exp.2 (by linarith)
    have h4 := (b3 a b).trans (mul_le_mul_of_nonneg_left h3 hC.le)
    have h5 := mul_le_mul_of_nonneg_right h4 (norm_nonneg A)
    have h6 : 0 ≤ C * (1 + |M₀|) * Real.exp (r / 2) := by positivity
    nlinarith
