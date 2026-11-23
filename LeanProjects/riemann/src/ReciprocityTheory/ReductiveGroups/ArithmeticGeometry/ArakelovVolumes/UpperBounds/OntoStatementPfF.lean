import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.OntoStatementPfC
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.OntoStatementPfD
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.OntoStatementPfE

namespace ReciprocityTheory.ChartRestriction.G.AR.Up.OntoF

open NumberField Complex Matrix Topology Filter MeasureTheory Set Metric ReciprocityTheory.ChartRestriction.G.FD
  ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.L2DbarEstimates ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Up.OntoB
  ReciprocityTheory.ChartRestriction.G.AR.Up.OntoC ReciprocityTheory.ChartRestriction.G.AR.Up.OntoE
open scoped ComplexConjugate ContDiff ENNReal

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r) (x0 : Frame X.Ψ r)

theorem sq_sub_le (a b : ℂ) : ‖b‖ ^ 2 ≤ 2 * ‖a‖ ^ 2 + 2 * ‖a - b‖ ^ 2 := by
  have h := norm_sub_le a (a - b)
  rw [sub_sub_cancel] at h
  nlinarith [sq_nonneg (‖a‖ - ‖a - b‖), norm_nonneg b, norm_nonneg a, norm_nonneg (a - b)]

theorem ball_diff_eq {g1 : V (nd X) → ℂ} {z : V (nd X)} {ρ : ℝ} (hB : ball z ρ ⊆ OmF X x0) :
    ball z ρ \ {y | g1 y = 0} = ball z ρ ∩ Om1 X x0 g1 := by
  ext y
  simp only [Set.mem_diff, Set.mem_inter_iff, Set.mem_setOf_eq, Om1]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h1, hB h1, h2⟩
  · rintro ⟨h1, -, h2⟩
    exact ⟨h1, h2⟩

theorem localRepresentationL2 {la : Wt X.Ψ r} {W : Frame X.Ψ r → ℝ≥0∞} {c : ℝ} (hc : 0 < c)
    (hWL : ∀ x ∈ X.dom, ENNReal.ofReal (c * Real.exp (-phla X la x)) ≤ W x) {bb : ℝ}
    {g1 : V (nd X) → ℂ} (hg1 : DifferentiableOn ℂ g1 (OmF X x0)) {F0 F' : V (nd X) → ℂ}
    (hF0 : ContinuousOn F0 (OmF X x0))
    (hJ : ∫⁻ z in Om1 X x0 g1, ENNReal.ofReal (‖F0 z - F' z‖ ^ 2 / kaF X x0 bb z) *
      W (cpt X x0 z) ∂muF X x0 < ⊤) :
    ∀ z ∈ OmF X x0, ∃ ρ > 0, ball z ρ ⊆ OmF X x0 ∧
      ∫⁻ y in ball z ρ \ {y | g1 y = 0}, ENNReal.ofReal (‖F' y‖ ^ 2) < ⊤ := by
  intro z hz
  obtain ⟨ε, hε, hεB⟩ := Metric.isOpen_iff.1 (isOpen_OmF (X := X) (x0 := x0)) z hz
  set ρ := ε / 2 with hρ
  have hρ0 : 0 < ρ := by positivity
  have hKsub : closedBall z ρ ⊆ OmF X x0 := (closedBall_subset_ball (by linarith)).trans hεB
  have hBsub : ball z ρ ⊆ OmF X x0 := ball_subset_closedBall.trans hKsub
  have hKc : IsCompact (closedBall z ρ) := isCompact_closedBall z ρ
  have hzK : z ∈ closedBall z ρ := mem_closedBall_self hρ0.le
  refine ⟨ρ, hρ0, hBsub, ?_⟩
  rw [ball_diff_eq X x0 hBsub]

  obtain ⟨M0, hM0⟩ := hKc.exists_bound_of_continuousOn (hF0.mono hKsub)
  have hgc : ContinuousOn (fun y => c * Real.exp (-phla X la (cpt X x0 y))) (closedBall z ρ) :=
    (continuousOn_const.mul (expPhla_cont (X := X) (x0 := x0) la)).mono hKsub
  obtain ⟨y1, -, hy1⟩ := hKc.exists_isMinOn ⟨z, hzK⟩ hgc
  set w0 := c * Real.exp (-phla X la (cpt X x0 y1)) with hw0
  have hw0p : 0 < w0 := by positivity
  have hdc : ContinuousOn (densF X x0) (closedBall z ρ) := (densF_continuousOn (X := X) (x0 := x0)).mono hKsub
  obtain ⟨y2, hy2K, hy2⟩ := hKc.exists_isMinOn ⟨z, hzK⟩ hdc
  set d0 := densF X x0 y2 with hd0
  have hd0p : 0 < d0 := densF_pos (X := X) (x0 := x0) (hKsub hy2K)
  have hkc : ContinuousOn (kaF X x0 bb) (closedBall z ρ) := fun y hy =>
    (ka_contDiffAt (X := X) (x0 := x0) bb (hKsub hy)).continuousAt.continuousWithinAt
  obtain ⟨k1, hk1⟩ := hKc.exists_bound_of_continuousOn hkc
  set kmax := max k1 1 with hkmax
  have hka : ∀ y ∈ closedBall z ρ, 0 < kaF X x0 bb y ∧ kaF X x0 bb y ≤ kmax := fun y hy => by
    have hp : 0 < kaF X x0 bb y := Real.exp_pos _
    refine ⟨hp, ?_⟩
    have := hk1 y hy
    rw [Real.norm_eq_abs, abs_of_pos hp] at this
    exact this.trans (le_max_left _ _)

  have hOm1o : IsOpen (Om1 X x0 g1) :=
    hg1.continuousOn.isOpen_inter_preimage (isOpen_OmF (X := X) (x0 := x0)) isOpen_compl_singleton
  have hOm1m : MeasurableSet (Om1 X x0 g1) := hOm1o.measurableSet
  have hOm1s : Om1 X x0 g1 ⊆ OmF X x0 := fun y hy => hy.1
  set dd : V (nd X) → ℝ≥0∞ := fun y => ENNReal.ofReal (densF X x0 y) with hdd
  set h : V (nd X) → ℝ≥0∞ := fun y =>
    ENNReal.ofReal (‖F0 y - F' y‖ ^ 2 / kaF X x0 bb y) * W (cpt X x0 y) with hh
  have hJ' : ∫⁻ y in Om1 X x0 g1, dd y * h y < ⊤ := by
    have e : ∫⁻ y in Om1 X x0 g1, h y ∂muF X x0 = ∫⁻ y in Om1 X x0 g1, dd y * h y := by
      rw [muF, restrict_withDensity hOm1m, Measure.restrict_restrict hOm1m, Set.inter_eq_left.2 hOm1s]
      exact lintegral_withDensity_eq_lintegral_mul_non_measurable₀ _
        (((densF_continuousOn (X := X) (x0 := x0)).mono hOm1s).aemeasurable hOm1m).ennreal_ofReal
        (ae_of_all _ fun _ => ENNReal.ofReal_lt_top) h
    rw [← e]
    exact hJ
  set Cst : ℝ := 2 * kmax / (w0 * d0) with hCst
  have hpt : ∀ y ∈ ball z ρ ∩ Om1 X x0 g1, ENNReal.ofReal (‖F' y‖ ^ 2) ≤
      ENNReal.ofReal (2 * M0 ^ 2) + ENNReal.ofReal Cst * (dd y * h y) := by
    rintro y ⟨hyB, -⟩
    have hyK : y ∈ closedBall z ρ := ball_subset_closedBall hyB
    have hyF : y ∈ OmF X x0 := hKsub hyK
    obtain ⟨hk0, hkle⟩ := hka y hyK
    have hdy : d0 ≤ densF X x0 y := hy2 hyK
    have hwy : w0 ≤ c * Real.exp (-phla X la (cpt X x0 y)) := hy1 hyK
    have hW : ENNReal.ofReal w0 ≤ W (cpt X x0 y) := (ENNReal.ofReal_le_ofReal hwy).trans (hWL _ hyF)
    have hq : 0 ≤ ‖F0 y - F' y‖ ^ 2 := by positivity
    have hM2 : ‖F0 y‖ ^ 2 ≤ M0 ^ 2 := pow_le_pow_left₀ (norm_nonneg _) (hM0 y hyK) 2
    have hsq := sq_sub_le (F0 y) (F' y)
    have f1 : 1 ≤ kmax / kaF X x0 bb y := (one_le_div hk0).2 hkle
    have f2 : 1 ≤ densF X x0 y / d0 := (one_le_div hd0p).2 hdy
    have hdens : 0 ≤ densF X x0 y := hd0p.le.trans hdy
    have hCst0 : 0 ≤ Cst := by positivity
    have hreal : 2 * ‖F0 y - F' y‖ ^ 2 ≤
        Cst * densF X x0 y * (‖F0 y - F' y‖ ^ 2 / kaF X x0 bb y) * w0 := by
      have e : Cst * densF X x0 y * (‖F0 y - F' y‖ ^ 2 / kaF X x0 bb y) * w0 =
          2 * ‖F0 y - F' y‖ ^ 2 * ((kmax / kaF X x0 bb y) * (densF X x0 y / d0)) := by
        rw [hCst]
        field_simp
      rw [e]
      have f3 : 1 ≤ (kmax / kaF X x0 bb y) * (densF X x0 y / d0) := by nlinarith
      nlinarith
    calc ENNReal.ofReal (‖F' y‖ ^ 2)
        ≤ ENNReal.ofReal (2 * M0 ^ 2 + 2 * ‖F0 y - F' y‖ ^ 2) := ENNReal.ofReal_le_ofReal (by linarith)
      _ = ENNReal.ofReal (2 * M0 ^ 2) + ENNReal.ofReal (2 * ‖F0 y - F' y‖ ^ 2) :=
          ENNReal.ofReal_add (by positivity) (by positivity)
      _ ≤ ENNReal.ofReal (2 * M0 ^ 2) + ENNReal.ofReal Cst * (dd y * h y) := by
          gcongr ENNReal.ofReal (2 * M0 ^ 2) + ?_
          calc ENNReal.ofReal (2 * ‖F0 y - F' y‖ ^ 2)
              ≤ ENNReal.ofReal (Cst * densF X x0 y * (‖F0 y - F' y‖ ^ 2 / kaF X x0 bb y) * w0) :=
                ENNReal.ofReal_le_ofReal hreal
            _ = ENNReal.ofReal Cst * (ENNReal.ofReal (densF X x0 y) *
                  (ENNReal.ofReal (‖F0 y - F' y‖ ^ 2 / kaF X x0 bb y) * ENNReal.ofReal w0)) := by
                rw [ENNReal.ofReal_mul (mul_nonneg (mul_nonneg hCst0 hdens) (div_nonneg hq hk0.le)),
                  ENNReal.ofReal_mul (mul_nonneg hCst0 hdens), ENNReal.ofReal_mul hCst0]
                ring
            _ ≤ ENNReal.ofReal Cst * (dd y * h y) := by
                show _ ≤ ENNReal.ofReal Cst * (ENNReal.ofReal (densF X x0 y) *
                  (ENNReal.ofReal (‖F0 y - F' y‖ ^ 2 / kaF X x0 bb y) * W (cpt X x0 y)))
                gcongr
  calc ∫⁻ y in ball z ρ ∩ Om1 X x0 g1, ENNReal.ofReal (‖F' y‖ ^ 2)
      ≤ ∫⁻ y in ball z ρ ∩ Om1 X x0 g1, (ENNReal.ofReal (2 * M0 ^ 2) + ENNReal.ofReal Cst * (dd y * h y)) :=
        setLIntegral_mono' (measurableSet_ball.inter hOm1m) hpt
    _ = ENNReal.ofReal (2 * M0 ^ 2) * volume (ball z ρ ∩ Om1 X x0 g1) +
          ENNReal.ofReal Cst * ∫⁻ y in ball z ρ ∩ Om1 X x0 g1, dd y * h y := by
        rw [lintegral_add_left measurable_const, lintegral_const,
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, Measure.restrict_apply_univ]
    _ < ⊤ := by
        apply ENNReal.add_lt_top.2 ⟨?_, ?_⟩
        · exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top
            ((measure_mono Set.inter_subset_left).trans_lt measure_ball_lt_top)
        · exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top
            ((lintegral_mono_set Set.inter_subset_right).trans_lt hJ')

end

end ReciprocityTheory.ChartRestriction.G.AR.Up.OntoF
