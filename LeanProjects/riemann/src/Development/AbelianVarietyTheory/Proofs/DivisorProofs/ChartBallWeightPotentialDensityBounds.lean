import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.WeightFunctionOnFrames
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.KaUnfoldPfC
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.InterpStatementPfM
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.DifferentiableChart
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.FirstMinimumInvariantContinuousPosOnFrames
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormFactorAndDensityNearOneInFlagChart
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GramChartSubFormEntryLe
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal Matrix

namespace GlobalTheory.WeightSizes

theorem chart_ball_sizes : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (la : Wt X.Ψ r) (x : Frame X.Ψ r) (z : V (nd X)), IsOrth X x → ‖z‖ ≤ 1 / (100 * (r : ℝ) ^ 2) → z ∈ OmF X x ∧ |phla X la (cpt X x z)| ≤ ∑ τ, ∑ a, |(la τ a : ℝ)| ∧ |rhF X x z| ≤ (X.Ψ.card : ℝ) ∧ |Real.log (densF X x z)| ≤ (X.Ψ.card : ℝ) * r ∧ 0 < densF X x z := by
  intro E _ _ _ r X la x z hx hz
  have h : (r : ℝ) ^ 2 * ‖z‖ ≤ 1 / 100 := by
    rcases Nat.eq_zero_or_pos r with rfl | hr
    · norm_num
    · have hr' : (0 : ℝ) < (r : ℝ) ^ 2 := by positivity
      calc (r : ℝ) ^ 2 * ‖z‖ ≤ (r : ℝ) ^ 2 * (1 / (100 * (r : ℝ) ^ 2)) :=
            mul_le_mul_of_nonneg_left hz hr'.le
        _ = 1 / 100 := by field_simp
  obtain ⟨hdom, hd⟩ := GlobalTheory.dmin_rmul_near_one X x hx (nmat X z) (norm_nonneg z) (by linarith)
    (fun τ a b => GlobalTheory.ChartNearOne.nmat_entry_le X z τ a b)
  change cpt X x z ∈ X.dom at hdom
  have hL : ∀ τ i, |IW.Lm X (cpt X x z) τ i| ≤ 9 / 100 := fun τ i => by
    have h9 := (hd τ i).2
    change |Real.log ‖dmin X.Gm (cpt X x z) τ i‖| ≤ _ at h9
    unfold IW.Lm
    linarith
  have hz' : z ∈ OmF X x := hdom
  refine ⟨hz', ?_, ?_, ?_, ?_⟩
  · rw [IW.phla_eq X hdom la]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun τ _ => ?_)
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
    rw [abs_mul]
    have h1 : |IW.Lm X (cpt X x z) τ i.succ - IW.Lm X (cpt X x z) τ i.castSucc| ≤ 1 := by
      have ha := abs_le.1 (hL τ i.succ)
      have hb := abs_le.1 (hL τ i.castSucc)
      rw [abs_le]
      constructor <;> linarith [ha.1, ha.2, hb.1, hb.2]
    calc |(la τ i : ℝ)| * _ ≤ |(la τ i : ℝ)| * 1 := mul_le_mul_of_nonneg_left h1 (abs_nonneg _)
      _ = _ := mul_one _
  · unfold rhF
    rw [abs_neg]
    have hs : ∑ τ : X.Ψ, |Real.log ‖dmin X.Gm (cpt X x z) τ ⟨X.p0, Nat.lt_succ_of_le X.p0_le⟩‖| ≤
        ∑ _τ : X.Ψ, (1 : ℝ) := Finset.sum_le_sum fun τ _ => by
      have h9 := hL τ ⟨X.p0, Nat.lt_succ_of_le X.p0_le⟩
      unfold IW.Lm at h9
      linarith
    refine (Finset.abs_sum_le_sum_abs _ _).trans (hs.trans ?_)
    simp
  · rw [IW.log_densF_eq X x hz']
    have hs : ∑ τ : X.Ψ, ∑ i : Fin r, |(-2) * IW.Lm X (cpt X x z) τ i.castSucc| ≤
        ∑ _τ : X.Ψ, ∑ _i : Fin r, (1 : ℝ) := Finset.sum_le_sum fun τ _ => Finset.sum_le_sum fun i _ => by
      have h9 := hL τ i.castSucc
      rw [abs_mul]
      norm_num
      linarith
    refine (Finset.abs_sum_le_sum_abs _ _).trans
      ((Finset.sum_le_sum fun τ _ => Finset.abs_sum_le_sum_abs _ _).trans (hs.trans ?_))
    simp
  · unfold densF
    exact Finset.prod_pos fun τ _ => Finset.prod_pos fun i _ =>
      zpow_pos (norm_pos_iff.2 (IW.dmin_ne_zero X hdom τ _)) _

end GlobalTheory.WeightSizes
