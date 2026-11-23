import Mathlib
import ReciprocityTheory.L2DbarEstimates.Imports
import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.FourSignHolds
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.L2ExtensionLogCanonical
import Development.AbelianVarietyTheory.Definitions.Divisors.EtaleEmpty
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PshNormalFrameQuadraticComparisonStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPeakSectionSmallDbarEnergyStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinSumSmoothSectionDbarEnergyLeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PosLowerBoundOnFinset
open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff

namespace GlobalTheory.OTY

theorem peakFin_exists_pos_le {Y : Type} (T : Finset Y) (f : Y → ℝ) (hf : ∀ P, 0 < f P) :
    ∃ r : ℝ, 0 < r ∧ ∀ P ∈ T, r ≤ f P := by
  first
  | exact @_root_.GlobalTheory.PositiveLowerBoundFinset.pos_lower_bound_on_finset
  | exact _root_.GlobalTheory.PositiveLowerBoundFinset.pos_lower_bound_on_finset
  | (apply _root_.GlobalTheory.PositiveLowerBoundFinset.pos_lower_bound_on_finset <;> assumption)
  | (intros; apply _root_.GlobalTheory.PositiveLowerBoundFinset.pos_lower_bound_on_finset <;> assumption)
  | (intros; apply @_root_.GlobalTheory.PositiveLowerBoundFinset.pos_lower_bound_on_finset <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.PositiveLowerBoundFinset.pos_lower_bound_on_finset ..)

theorem peak_sections_finite : ∀ (n : ℕ) (Y : Type) [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] (ι La : Type) [AddCommGroup La] (A : WeightedAtlas n Y ι La), ∀ (C : Cover A), ∀ (H : La), (∀ i y, y ∈ (A.chart i).source → ∀ ξ : Fin n → ℂ, ξ ≠ 0 → 0 < A.leviAt i (A.ph H i) y ξ) → ∀ T : Finset Y, ∃ (q : Y → V n → ℂ) (c Cq r0 : ℝ), 0 < c ∧ 0 < r0 ∧ (∀ P ∈ T, Differentiable ℂ (q P) ∧ closedBall (A.chart (A.pick P) P) r0 ⊆ (A.chart (A.pick P)).target ∧ ∀ v ∈ closedBall (A.chart (A.pick P) P) r0, A.ph H (A.pick P) ((A.chart (A.pick P)).symm v) - 2 * (q P v).re ≤ Cq * ‖v - (A.chart (A.pick P) P)‖ ^ 2) ∧ ∀ (G : La) (p : Y → V n → ℂ), (∀ P, Differentiable ℂ (p P)) → ∃ K : ℝ, 0 ≤ K ∧ ∀ k : ℕ, ∃ F0 : ι → Y → ℂ, A.IsSSec (A.kap + (G + k • H)) F0 ∧ (∀ P ∈ T, ∀ v ∈ ball (A.chart (A.pick P) P) r0, F0 (A.pick P) ((A.chart (A.pick P)).symm v) = p P v * Complex.exp (k * q P v)) ∧ n1 C (G + k • H) F0 ≤ ENNReal.ofReal (K * Real.exp (-c * k)) := by
  intro n Y _ _ _ _ _ ι La _ A C H hH T
  classical
  obtain ⟨U, hU, hdisj⟩ := T.finite_toSet.t2_separation
  have h7 : ∀ P : Y, ∃ (q : V n → ℂ) (c C ρ : ℝ), Differentiable ℂ q ∧ 0 < c ∧ 0 < C ∧ 0 < ρ ∧
      closedBall (A.chart (A.pick P) P) ρ ⊆
        (A.chart (A.pick P)).target ∩ (A.chart (A.pick P)).symm ⁻¹' U P ∧
      ∀ v ∈ closedBall (A.chart (A.pick P) P) ρ,
        c * ‖v - A.chart (A.pick P) P‖ ^ 2 ≤
          A.ph H (A.pick P) ((A.chart (A.pick P)).symm v) - 2 * (q v).re ∧
        A.ph H (A.pick P) ((A.chart (A.pick P)).symm v) - 2 * (q v).re ≤
          C * ‖v - A.chart (A.pick P) P‖ ^ 2 := by
    intro P
    refine GlobalTheory.T.psh_normal_frame_quadratic_comparison n _ (fun v => A.ph H (A.pick P) ((A.chart (A.pick P)).symm v)) _
      ((A.chart (A.pick P)).isOpen_inter_preimage_symm (hU P).2) ?_
      ((A.smooth_ph H (A.pick P)).mono Set.inter_subset_left) ?_
    · refine ⟨(A.chart (A.pick P)).map_source (A.mem_pick P), ?_⟩
      rw [Set.mem_preimage, (A.chart (A.pick P)).left_inv (A.mem_pick P)]
      exact (hU P).1
    · intro ξ hξ
      exact hH (A.pick P) P (A.mem_pick P) ξ hξ
  choose q c Cc ρ hq hc hC hρ hsub hb using h7
  obtain ⟨r0, hr0, hr0le⟩ := peakFin_exists_pos_le T (fun P => ρ P / 2)
    (fun P => half_pos (hρ P))
  obtain ⟨c0, hc0, hc0le⟩ := peakFin_exists_pos_le T (fun P => c P * ρ P ^ 2 / 4)
    (fun P => by have := hc P; have := hρ P; positivity)
  have hrρ : ∀ P ∈ T, r0 ≤ ρ P := fun P hP => by
    have h1 : r0 ≤ ρ P / 2 := hr0le P hP
    have := hρ P
    linarith
  refine ⟨q, c0, ∑ P ∈ T, Cc P, r0, hc0, hr0, fun P hP => ⟨hq P, ?_, ?_⟩, ?_⟩
  · exact ((closedBall_subset_closedBall (hrρ P hP)).trans (hsub P)).trans Set.inter_subset_left
  · intro v hv
    refine (hb P v (closedBall_subset_closedBall (hrρ P hP) hv)).2.trans ?_
    exact mul_le_mul_of_nonneg_right
      (Finset.single_le_sum (f := Cc) (fun Q _ => (hC Q).le) hP) (by positivity)
  · intro G p hp
    have h9 := fun P : Y => GlobalTheory.T.exists_peak_section_small_dbar_energy n Y ι La A C H G (A.pick P) (A.chart (A.pick P) P)
      (ρ P) (c P) (q P) (p P) (hρ P) (hc P) ((hsub P).trans Set.inter_subset_left) (hq P) (hp P)
      (fun v hv => (hb P v hv).1)
    choose K hK F hF using h9
    have hKs : 0 ≤ ∑ P ∈ T, K P := Finset.sum_nonneg fun P _ => hK P
    refine ⟨(T.card : ℝ) * ∑ P ∈ T, K P, by positivity, fun k => ?_⟩
    obtain ⟨hs, hn⟩ := GlobalTheory.T.finSum_smoothSection_dbarEnergy_le n Y ι La A C (G + k • H) T (fun P => F P k)
      (fun P _ => (hF P k).1)
    refine ⟨_, hs, fun P hP v hv => ?_, hn.trans ?_⟩
    · have hv' : v ∈ ball (A.chart (A.pick P) P) (ρ P / 2) := ball_subset_ball (hr0le P hP) hv
      have hvU : (A.chart (A.pick P)).symm v ∈ U P :=
        (hsub P (ball_subset_closedBall (ball_subset_ball (hrρ P hP) hv))).2
      rw [← (hF P k).2.1 v hv']
      refine Finset.sum_eq_single_of_mem P hP (fun Q hQ hQP => ?_)
      refine (hF Q k).2.2.1 _ _ (fun hm => ?_)
      have h1 := (hsub Q (ball_subset_closedBall hm.2)).2
      rw [Set.mem_preimage, (A.chart (A.pick Q)).left_inv hm.1] at h1
      exact Set.disjoint_left.1 (hdisj (Finset.mem_coe.2 hQ) (Finset.mem_coe.2 hP) hQP) h1 hvU
    · have hle : ∑ P ∈ T, n1 C (G + k • H) (F P k) ≤
          ∑ P ∈ T, ENNReal.ofReal (K P * Real.exp (-c0 * k)) := by
        refine Finset.sum_le_sum fun P hP => (hF P k).2.2.2.trans ?_
        refine ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left ?_ (hK P))
        refine Real.exp_le_exp.2 (mul_le_mul_of_nonneg_right ?_ (Nat.cast_nonneg k))
        exact neg_le_neg (hc0le P hP)
      refine (mul_le_mul_right hle _).trans (le_of_eq ?_)
      rw [← ENNReal.ofReal_sum_of_nonneg
          (fun P _ => mul_nonneg (hK P) (Real.exp_pos _).le), ← Finset.sum_mul, mul_assoc,
        ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast]

end GlobalTheory.OTY
