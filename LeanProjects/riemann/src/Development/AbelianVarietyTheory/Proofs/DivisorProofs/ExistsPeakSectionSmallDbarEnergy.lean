import Mathlib
import ReciprocityTheory.L2DbarEstimates.Imports
import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.FourSignHolds
import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.AApproxB
import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.APrimeI
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.L2ExtensionLogCanonical
import Development.AbelianVarietyTheory.Definitions.Divisors.EtaleEmpty
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothSectionCutoffMulHolomorphicStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DbarEnergyCutoffMulSectionLeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothBumpChartBallHalfOneStatement

open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff

namespace GlobalTheory.OTY

theorem peak_isSecOn {n : ℕ} {Y : Type} [TopologicalSpace Y] [T2Space Y]
    [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] {ι La : Type} [AddCommGroup La]
    (A : WeightedAtlas n Y ι La) (la : La) (i : ι) (W : Set Y) (hW : W ⊆ (A.chart i).source)
    (u : V n → ℂ) (hu : Differentiable ℂ u) :
    A.IsSecOn la W (fun j y => A.g la j i y * u (A.chart i y)) := by
  refine ⟨fun j => ?_, fun j l y hy hj hl => ?_⟩
  · have hsub : (A.chart j).target ∩ (A.chart j).symm ⁻¹' W ⊆ ovl A.chart j i :=
      fun v hv => ⟨hv.1, hW hv.2⟩
    have h1 := (A.holo_g la j i).mono hsub
    have h2 := hu.comp_differentiableOn ((A.holo_trans j i).mono hsub)
    exact h1.mul h2
  · show A.g la j i y * _ = A.g la j l y * (A.g la l i y * _)
    rw [A.g_cocycle la j l i y hj hl (hW hy)]; ring

theorem peak_section : ∀ (n : ℕ) (Y : Type) [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] (ι La : Type) [AddCommGroup La] (A : WeightedAtlas n Y ι La), ∀ (C : Cover A) (H G : La) (i : ι) (p : V n) (ρ c : ℝ) (q f : V n → ℂ), 0 < ρ → 0 < c → closedBall p ρ ⊆ (A.chart i).target → Differentiable ℂ q → Differentiable ℂ f → (∀ v ∈ closedBall p ρ, c * ‖v - p‖ ^ 2 ≤ A.ph H i ((A.chart i).symm v) - 2 * (q v).re) → ∃ K : ℝ, 0 ≤ K ∧ ∀ k : ℕ, ∃ F0 : ι → Y → ℂ, A.IsSSec (A.kap + (G + k • H)) F0 ∧ (∀ v ∈ ball p (ρ / 2), F0 i ((A.chart i).symm v) = f v * Complex.exp (k * q v)) ∧ (∀ j y, y ∉ (A.chart i).source ∩ A.chart i ⁻¹' ball p ρ → F0 j y = 0) ∧ n1 C (G + k • H) F0 ≤ ENNReal.ofReal (K * Real.exp (-(c * ρ ^ 2 / 4) * k)) := by
  intro n Y _ _ _ _ _ ι La _ A C H G i p ρ c q f hρ hc hball hq hf hpeak
  obtain ⟨χ, hχs, hχsupp, hχ1⟩ := GlobalTheory.T.smooth_bump_chart_ball_halfOne n Y ι La A i p ρ hρ hball
  obtain ⟨K0, hK0, hcut⟩ := GlobalTheory.T.n1_cutoff_mul_section_le_lintegral n Y ι La A C χ hχs
  set W : Set Y := (A.chart i).source ∩ A.chart i ⁻¹' ball p ρ with hWdef
  set Wi : Set Y := (A.chart i).source ∩ A.chart i ⁻¹' ball p (ρ / 2) with hWidef
  have hWo : IsOpen W := (A.chart i).isOpen_inter_preimage isOpen_ball
  have hWio : IsOpen Wi := (A.chart i).isOpen_inter_preimage isOpen_ball
  have hWs : W ⊆ (A.chart i).source := Set.inter_subset_left
  set Z : Set Y := W \ Wi with hZdef
  have hZm : MeasurableSet Z := hWo.measurableSet.diff hWio.measurableSet
  have hZloc : ∀ y, y ∉ Z → ∀ᶠ x in 𝓝 y, χ x = χ y := by
    intro y hy
    by_cases hyW : y ∈ W
    · have hyi : y ∈ Wi := by
        by_contra h
        exact hy ⟨hyW, h⟩
      filter_upwards [hWio.mem_nhds hyi] with x hx
      rw [hχ1 x hx.1 hx.2, hχ1 y hyi.1 hyi.2]
    · have hns : y ∉ tsupport χ := fun h => hyW (hχsupp h)
      filter_upwards [(isClosed_tsupport χ).isOpen_compl.mem_nhds hns] with x hx
      rw [image_eq_zero_of_notMem_tsupport hx, image_eq_zero_of_notMem_tsupport hns]
  have hKc : IsCompact ((A.chart i).symm '' closedBall p ρ) :=
    (isCompact_closedBall p ρ).image_of_continuousOn ((A.chart i).continuousOn_symm.mono hball)
  have hWK : Z ∩ W ⊆ (A.chart i).symm '' closedBall p ρ := fun y hy =>
    ⟨A.chart i y, ball_subset_closedBall hy.2.2, (A.chart i).left_inv hy.2.1⟩
  have hfin : A.mu (Z ∩ W) ≠ ⊤ :=
    ((measure_mono hWK).trans_lt (ap_mu_compact A _ hKc)).ne
  have hcont : ContinuousOn (fun v => ‖f v‖ ^ 2 *
      Real.exp (-A.ph (A.kap + G) i ((A.chart i).symm v))) (closedBall p ρ) :=
    (hf.continuous.continuousOn.norm.pow 2).mul
      (((A.smooth_ph (A.kap + G) i).continuousOn.mono hball).neg.rexp)
  obtain ⟨M, hM⟩ := (isCompact_closedBall p ρ).exists_bound_of_continuousOn hcont
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM p (mem_closedBall_self hρ.le))
  refine ⟨K0 * (M * (A.mu (Z ∩ W)).toReal), by positivity, fun k => ?_⟩
  have hu : Differentiable ℂ (fun v => f v * Complex.exp (k * q v)) :=
    hf.mul ((hq.const_mul _).cexp)
  have hsec := peak_isSecOn A (A.kap + (G + k • H)) i W hWs _ hu
  refine ⟨_, GlobalTheory.T.smoothSection_cutoff_mul_holomorphic n Y ι La A _ W χ _ hWo hχs hχsupp hsec, ?_, ?_, ?_⟩
  · intro v hv
    have hvt : v ∈ (A.chart i).target :=
      hball (ball_subset_closedBall (ball_subset_ball (by linarith) hv))
    have hs := (A.chart i).map_target hvt
    have hr := (A.chart i).right_inv hvt
    have h1 : χ ((A.chart i).symm v) = 1 := hχ1 _ hs (by rw [hr]; exact hv)
    simp only [h1, A.g_self _ i hs, hr]
    simp
  · intro j y hy
    have hns : y ∉ tsupport χ := fun h => hy (hχsupp h)
    simp [image_eq_zero_of_notMem_tsupport hns]
  · refine (hcut (G + k • H) W Z _ hWo hχsupp hsec hZm hZloc).trans ?_
    have hbd : ∀ y ∈ Z ∩ W, ENNReal.ofReal (A.nsq (A.kap + (G + k • H))
        (fun j y => A.g (A.kap + (G + k • H)) j i y *
          (f (A.chart i y) * Complex.exp (k * q (A.chart i y)))) y) ≤
        ENNReal.ofReal (M * Real.exp (-(c * ρ ^ 2 / 4) * k)) := by
      intro y hy
      apply ENNReal.ofReal_le_ofReal
      have hs : y ∈ (A.chart i).source := hy.2.1
      have hcb : A.chart i y ∈ closedBall p ρ := ball_subset_closedBall hy.2.2
      have hout : ρ / 2 ≤ ‖A.chart i y - p‖ := by
        by_contra h
        exact hy.1.2 ⟨hs, by simpa [mem_ball, dist_eq_norm] using not_le.1 h⟩
      rw [A.nsq_chart _ _ i hs (hsec.2 _ i y hy.2 (A.mem_pick y) hs)]
      have h1 := hM _ hcb
      have h2 := hpeak _ hcb
      rw [(A.chart i).left_inv hs] at h1 h2
      rw [Real.norm_of_nonneg (by positivity)] at h1
      have h3 : c * ρ ^ 2 / 4 ≤ c * ‖A.chart i y - p‖ ^ 2 := by
        have : (ρ / 2) ^ 2 ≤ ‖A.chart i y - p‖ ^ 2 := by gcongr
        nlinarith
      have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
      have e : ‖A.g (A.kap + (G + k • H)) i i y *
          (f (A.chart i y) * Complex.exp (k * q (A.chart i y)))‖ ^ 2 *
          Real.exp (-A.ph (A.kap + (G + k • H)) i y) =
          (‖f (A.chart i y)‖ ^ 2 * Real.exp (-A.ph (A.kap + G) i y)) *
          Real.exp (-(A.ph H i y - 2 * (q (A.chart i y)).re) * k) := by
        rw [A.g_self _ i hs, one_mul, norm_mul, Complex.norm_exp, ← add_assoc,
          A.ph_add _ (k • H) i y hs, A.aap_ph_nsmul H k i hs, mul_pow, ← Real.exp_nat_mul,
          mul_assoc, mul_assoc, ← Real.exp_add, ← Real.exp_add]
        congr 2
        simp
        ring
      refine e.le.trans ?_
      refine mul_le_mul h1 (Real.exp_le_exp.2 ?_) (Real.exp_pos _).le hM0
      nlinarith
    have hint := setLIntegral_mono' (μ := A.mu) (hZm.inter hWo.measurableSet) hbd
    rw [setLIntegral_const] at hint
    refine (mul_le_mul_right hint _).trans (le_of_eq ?_)
    rw [← ENNReal.ofReal_toReal hfin, ← ENNReal.ofReal_mul (by positivity),
      ← ENNReal.ofReal_mul hK0, ENNReal.toReal_ofReal ENNReal.toReal_nonneg]
    congr 1
    ring

end GlobalTheory.OTY
