import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsChartIbpSteps
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.ChartCutoffParts
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PChartEnergyIntegrable
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PHermFormCompare
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.AnForm ReciprocityTheory.AnForm.A Matrix MeasureTheory Filter Topology
open ChartIntegrationByPartsSymmetry
open scoped ComplexOrder

noncomputable section

namespace ChartIntegrationByPartsCutoff

variable {n : ℕ}

theorem sqrt_mul_sqrt_le {a b ε : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hε : 0 < ε) :
    Real.sqrt a * Real.sqrt b ≤ ε * a + b / (4 * ε) := by
  have h1 := Real.sq_sqrt ha
  have h2 := Real.sq_sqrt hb
  have h3 := sq_nonneg (2 * ε * Real.sqrt a - Real.sqrt b)
  have h4 : 0 < 4 * ε := by positivity
  have key : 4 * ε * (Real.sqrt a * Real.sqrt b) ≤ 4 * ε * (ε * a + b / (4 * ε)) := by
    rw [mul_add, mul_div_cancel₀ _ h4.ne']
    have e : (2 * ε * Real.sqrt a - Real.sqrt b) ^ 2 =
        4 * ε * (ε * a) + b - 4 * ε * (Real.sqrt a * Real.sqrt b) := by
      rw [sub_sq, mul_pow, mul_pow, h1, h2]
      ring
    linarith
  exact le_of_mul_le_mul_left key h4

def outer (n k : ℕ) : Set (Fin (n + 1) → ℂ) := {y | ((k : ℝ) + 1) ^ 2 ≤ ∑ i, ‖y i‖ ^ 2}

theorem measurableSet_outer (k : ℕ) : MeasurableSet (outer n k) :=
  (isClosed_le continuous_const (continuous_finsetSum _ fun i _ =>
    (continuous_norm.comp (continuous_apply i)).pow 2)).measurableSet

theorem tendsto_integral_outer {g : (Fin (n + 1) → ℂ) → ℝ} (hg : Integrable g) :
    Tendsto (fun k : ℕ => ∫ y, (outer n k).indicator g y) atTop (𝓝 0) := by
  have h0 : (∫ _y : Fin (n + 1) → ℂ, (0 : ℝ)) = 0 := integral_zero _ _
  rw [← h0]
  refine tendsto_integral_of_dominated_convergence (fun y => ‖g y‖)
    (fun k => (hg.indicator (measurableSet_outer k)).aestronglyMeasurable) hg.norm
    (fun k => Eventually.of_forall fun y => ?_) (Eventually.of_forall fun y => ?_)
  · rw [Set.indicator]
    split_ifs
    · exact le_rfl
    · simp
  · obtain ⟨N, hN⟩ := exists_nat_gt (∑ i, ‖y i‖ ^ 2)
    refine tendsto_atTop_of_eventually_const (i₀ := N) fun k hk => ?_
    have hk' : (N : ℝ) ≤ k := by exact_mod_cast hk
    have : ¬ y ∈ outer n k := by
      simp only [outer, Set.mem_ofPred_eq, not_le]
      nlinarith
    simp [Set.indicator_of_notMem this]

theorem tendsto_boundary {T : Fin n → Matrix (Fin (n + 1 + 1)) (Fin (n + 1 + 1)) ℂ} (hT : ∀ i, (T i).PosDef)
    {u w : (Fin (n + 1) → ℂ) → ℝ} {W : ℝ} (hW : ∀ y, ‖w y‖ ≤ W)
    (hE : Integrable (gradDens (fun i => hermChartPot (T i)) u u)) {K : ℝ}
    (hK : ∀ k : ℕ, ∫ y, gradDens (fun i => hermChartPot (T i)) (chartCutoff k) (chartCutoff k) y ≤ K) :
    Tendsto (fun k : ℕ => ∫ y, w y * gradDens (fun i => hermChartPot (T i)) (chartCutoff k) u y) atTop (𝓝 0) := by
  set φ : Fin n → (Fin (n + 1) → ℂ) → ℝ := fun i => hermChartPot (T i) with hφdef
  have h2 : ∀ i, ContDiff ℝ 2 (φ i) := fun i => contDiff_hermChartPot_of_le 2 (hT i)
  have hone : ((1 : ℕ) : WithTop ℕ∞) ≤ 3 := by norm_num
  have hW0 : 0 ≤ W := (norm_nonneg _).trans (hW 0)
  set t : ℕ → ℝ := fun k => ∫ y, (outer n k).indicator (gradDens φ u u) y with htdef
  have ht0 : ∀ k, 0 ≤ t k := fun k => integral_nonneg fun y =>
    Set.indicator_nonneg (fun y _ => gradDens_chart_nonneg hT u y) y
  set ε : ℕ → ℝ := fun k => Real.sqrt (t k + 1 / ((k : ℝ) + 1)) with hεdef
  have hεpos : ∀ k, 0 < ε k := fun k => Real.sqrt_pos.mpr (by have := ht0 k; positivity)
  have htε : ∀ k, t k ≤ ε k ^ 2 := fun k => by
    rw [hεdef, Real.sq_sqrt (by have := ht0 k; positivity)]
    have : (0 : ℝ) ≤ 1 / ((k : ℝ) + 1) := by positivity
    linarith
  have hbound : ∀ k, |∫ y, w y * gradDens φ (chartCutoff k) u y| ≤ W * (ε k * (K + 1 / 4)) := by
    intro k
    have hχ3 := contDiff_chartCutoff (D := n + 1) k 3
    have hcc := hasCompactSupport_chartCutoff (D := n + 1) k
    have hiχ : Integrable (gradDens φ (chartCutoff k) (chartCutoff k)) :=
      (continuous_gradDens h2 (hχ3.of_le hone) (hχ3.of_le hone)).integrable_of_hasCompactSupport
        (hasCompactSupport_gradDens_left φ _ hcc)
    have hiO : Integrable ((outer n k).indicator (gradDens φ u u)) := hE.indicator (measurableSet_outer k)
    have hpt : ∀ y, ‖w y * gradDens φ (chartCutoff k) u y‖ ≤
        W * (ε k * gradDens φ (chartCutoff k) (chartCutoff k) y +
          (outer n k).indicator (gradDens φ u u) y / (4 * ε k)) := by
      intro y
      rw [norm_mul]
      have hnn := gradDens_chart_nonneg hT (chartCutoff k) y
      by_cases hy : y ∈ outer n k
      · rw [Set.indicator_of_mem hy]
        have hcs : ‖gradDens φ (chartCutoff k) u y‖ ≤
            ε k * gradDens φ (chartCutoff k) (chartCutoff k) y + gradDens φ u u y / (4 * ε k) :=
          (abs_gradDens_chart_le hT (chartCutoff k) u y).trans
            (sqrt_mul_sqrt_le hnn (gradDens_chart_nonneg hT u y) (hεpos k))
        exact mul_le_mul (hW y) hcs (norm_nonneg _) hW0
      · have hlt : ∑ i, ‖y i‖ ^ 2 < ((k : ℝ) + 1) ^ 2 := by simpa [outer] using hy
        rw [gradDens_chartCutoff_left φ u hlt, Set.indicator_of_notMem hy, norm_zero, mul_zero, zero_div,
          add_zero]
        exact mul_nonneg hW0 (mul_nonneg (hεpos k).le hnn)
    have hint : Integrable fun y => W * (ε k * gradDens φ (chartCutoff k) (chartCutoff k) y +
        (outer n k).indicator (gradDens φ u u) y / (4 * ε k)) :=
      ((hiχ.const_mul (ε k)).add (hiO.div_const (4 * ε k))).const_mul W
    have h1 := norm_integral_le_of_norm_le hint (Eventually.of_forall hpt)
    rw [Real.norm_eq_abs] at h1
    refine h1.trans ?_
    rw [integral_const_mul, integral_add (hiχ.const_mul _) (hiO.div_const _), integral_const_mul, integral_div]
    refine mul_le_mul_of_nonneg_left ?_ hW0
    have hq : t k / (4 * ε k) ≤ ε k / 4 := by
      rw [div_le_div_iff₀ (by have := hεpos k; positivity) (by norm_num)]
      nlinarith [htε k, hεpos k]
    have := mul_le_mul_of_nonneg_left (hK k) (hεpos k).le
    change ε k * _ + t k / (4 * ε k) ≤ _
    nlinarith
  have htt : Tendsto t atTop (𝓝 0) := tendsto_integral_outer hE
  have hinv : Tendsto (fun k : ℕ => 1 / ((k : ℝ) + 1)) atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hε : Tendsto ε atTop (𝓝 0) := by
    have := ((htt.add hinv).sqrt)
    simpa [hεdef] using this
  have hB : Tendsto (fun k => W * (ε k * (K + 1 / 4))) atTop (𝓝 0) := by
    simpa using (hε.mul_const (K + 1 / 4)).const_mul W
  exact squeeze_zero_norm (fun k => (hbound k).trans_eq' (Real.norm_eq_abs _)) hB

end ChartIntegrationByPartsCutoff

open ChartIntegrationByPartsCutoff in

theorem ChartIbpCutoff.proof (hE : ChartCutoffEnergy.Statement) (hD : ChartDiffEnergy.Statement) :
    ChartIbpCutoff.Statement := by
  intro n A B C D T hA hB hC hD' hT
  set φ : Fin n → (Fin (n + 1) → ℂ) → ℝ := fun i => hermChartPot (T i) with hφdef
  set u : (Fin (n + 1) → ℂ) → ℝ := fun y => hermChartPot A y - hermChartPot B y with hudef
  set w : (Fin (n + 1) → ℂ) → ℝ := fun y => hermChartPot C y - hermChartPot D y with hwdef
  have h3 : ∀ i, ContDiff ℝ 3 (φ i) := fun i => contDiff_hermChartPot_of_le 3 (hT i)
  have hu : ContDiff ℝ 3 u := (contDiff_hermChartPot_of_le 3 hA).sub (contDiff_hermChartPot_of_le 3 hB)
  have hw : ContDiff ℝ 3 w := (contDiff_hermChartPot_of_le 3 hC).sub (contDiff_hermChartPot_of_le 3 hD')
  obtain ⟨Wu, hWu⟩ := ChartEnergyIntegrableAlt.pot_sub_bound HermFormCompare.proof hA hB
  obtain ⟨Ww, hWw⟩ := ChartEnergyIntegrableAlt.pot_sub_bound HermFormCompare.proof hC hD'
  obtain ⟨K, hK⟩ := hE n T hT
  have key : ∀ k : ℕ, (∫ y, chartCutoff k y * (u y * maDensity (Fin.cons w φ) y - w y * maDensity (Fin.cons u φ) y))
      = (∫ y, w y * gradDens φ (chartCutoff k) u y) - ∫ y, u y * gradDens φ (chartCutoff k) w y := by
    intro k
    obtain ⟨i1, -, -, e1⟩ := parts_cutoff h3 (contDiff_chartCutoff k 3) (hasCompactSupport_chartCutoff k) hu hw
    obtain ⟨i2, -, -, e2⟩ := parts_cutoff h3 (contDiff_chartCutoff k 3) (hasCompactSupport_chartCutoff k) hw hu
    have hsplit : ∀ y, chartCutoff k y * (u y * maDensity (Fin.cons w φ) y - w y * maDensity (Fin.cons u φ) y) =
        chartCutoff k y * u y * maDens (Fin.cons w φ) y - chartCutoff k y * w y * maDens (Fin.cons u φ) y :=
      fun y => by change _ = _ * _ * maDensity _ y - _ * _ * maDensity _ y; ring
    simp_rw [hsplit]
    rw [integral_sub i1 i2, e1, e2]
    simp_rw [show ∀ y, gradDens φ w u y = gradDens φ u w y from gradDens_chart_comm hT w u]
    ring
  refine Tendsto.congr (fun k => (key k).symm) ?_
  rw [← sub_zero (0 : ℝ)]
  exact (tendsto_boundary hT hWw (hD n A B T hA hB hT) hK).sub (tendsto_boundary hT hWu (hD n C D T hC hD' hT) hK)

end

end GroundTheory.Heights₂.Heights
