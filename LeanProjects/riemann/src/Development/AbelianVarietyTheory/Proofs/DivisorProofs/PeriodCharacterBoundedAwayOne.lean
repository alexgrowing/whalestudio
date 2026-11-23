import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.SiegelReframe
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SummableExpNegL1Norm
open Matrix MeasureTheory GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe GlobalTheory.TauPeriod Complex
open scoped Real ContDiff

noncomputable section

namespace GlobalTheory.TauPeriod

theorem per_single_inl {g : ℕ} (τ : Matrix (Fin g) (Fin g) ℂ) (k : Fin g) :
    per τ (Pi.single (Sum.inl k) 1) = fun i => τ k i := by
  ext i
  simp [per, vecMul, dotProduct, Pi.single_apply, apply_ite (fun t : ℝ => (t : ℂ)), ite_mul]

theorem le_norm_ex_sub_one {g : ℕ} (n : Fin g → ℤ) (z : Fin g → ℂ) {ε : ℝ} (hε : 0 < ε)
    (h : ε ≤ |∑ i, (n i : ℝ) * (z i).im|) :
    1 - Real.exp (-(2 * π * ε)) ≤ ‖ex n z - 1‖ := by
  have h1 : |‖ex n z‖ - ‖(1 : ℂ)‖| ≤ ‖ex n z - 1‖ := abs_norm_sub_norm_le _ _
  rw [norm_ex, norm_one] at h1
  refine le_trans ?_ h1
  set s := ∑ i, (n i : ℝ) * (z i).im
  have hpi := Real.pi_pos
  rcases le_abs'.1 h with hs | hs
  · have e0 : 2 * π * ε ≤ -(2 * π) * s := by nlinarith
    have e1 : 2 * π * ε + 1 ≤ Real.exp (-(2 * π) * s) := by
      have := Real.add_one_le_exp (-(2 * π) * s)
      linarith
    have e2 : 1 - Real.exp (-(2 * π * ε)) ≤ 2 * π * ε := by
      have := Real.add_one_le_exp (-(2 * π * ε)); linarith
    have e3 : 0 ≤ 2 * π * ε := by positivity
    rw [abs_of_nonneg (by linarith)]
    linarith
  · have e0 : -(2 * π) * s ≤ -(2 * π * ε) := by nlinarith
    have e1 : Real.exp (-(2 * π) * s) ≤ Real.exp (-(2 * π * ε)) := Real.exp_le_exp.2 e0
    rw [abs_sub_comm]
    calc 1 - Real.exp (-(2 * π * ε)) ≤ 1 - Real.exp (-(2 * π) * s) := by linarith
      _ ≤ |1 - Real.exp (-(2 * π) * s)| := le_abs_self _

theorem exists_entry_mulVec_ge {g : ℕ} (A : Matrix (Fin g) (Fin g) ℝ) (hA : IsUnit A.det) :
    ∃ c > 0, ∀ v : Fin g → ℝ, v ≠ 0 → ∃ k, c * ‖v‖ ≤ |(A *ᵥ v) k| := by
  set S : ℝ := ∑ j, ∑ k, |A⁻¹ j k| + 1 with hSdef
  have hS0 : 0 ≤ ∑ j, ∑ k, |A⁻¹ j k| := by positivity
  have hS : 0 < S := by linarith
  refine ⟨1 / S, by positivity, fun v hv => ?_⟩
  by_contra hne
  push_neg at hne
  have hpos : 0 < ‖v‖ := norm_pos_iff.2 hv
  have hinv : A⁻¹ *ᵥ (A *ᵥ v) = v := by
    rw [mulVec_mulVec, nonsing_inv_mul _ hA, one_mulVec]
  have : ‖v‖ < ‖v‖ := by
    refine (pi_norm_lt_iff hpos).2 fun j => ?_
    rw [Real.norm_eq_abs]
    have hrow : ∑ k, |A⁻¹ j k| ≤ S - 1 := by
      rw [hSdef, add_sub_cancel_right]
      exact Finset.single_le_sum (f := fun j => ∑ k, |A⁻¹ j k|)
        (fun _ _ => by positivity) (Finset.mem_univ j)
    calc |v j| = |∑ k, A⁻¹ j k * (A *ᵥ v) k| := by
          conv_lhs => rw [← hinv]
          rfl
      _ ≤ ∑ k, |A⁻¹ j k * (A *ᵥ v) k| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ k, |A⁻¹ j k| * (1 / S * ‖v‖) := by
          refine Finset.sum_le_sum fun k _ => ?_
          rw [abs_mul]
          exact mul_le_mul_of_nonneg_left (hne k).le (abs_nonneg _)
      _ = (∑ k, |A⁻¹ j k|) * (1 / S * ‖v‖) := by rw [Finset.sum_mul]
      _ ≤ (S - 1) * (1 / S * ‖v‖) := by
          exact mul_le_mul_of_nonneg_right hrow (by positivity)
      _ < ‖v‖ := by
          rw [show (S - 1) * (1 / S * ‖v‖) = ‖v‖ - ‖v‖ / S by field_simp]
          have : 0 < ‖v‖ / S := by positivity
          linarith
  exact lt_irrefl _ this

end GlobalTheory.TauPeriod

namespace GlobalTheory.TauPeriod

theorem exists_ball_norm_ex_row_sub_one_ge : ∀ {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [FiniteDimensional ℂ E] {g : ℕ} {U : Set E} {τ : E → Matrix (Fin g) (Fin g) ℂ},
    IsPeriodMap U τ → ∀ b₀ ∈ U, ∃ r > 0, Metric.closedBall b₀ r ⊆ U ∧ ∃ δ > 0,
      ∀ n : Fin g → ℤ, n ≠ 0 → ∃ k : Fin g, ∀ b ∈ Metric.closedBall b₀ r,
        δ ≤ ‖ex n (per (τ b) (Pi.single (Sum.inl k) 1)) - 1‖ := by
  intro E _ _ _ g U τ hτ b₀ hb₀
  obtain ⟨hU, hd, hs⟩ := hτ
  set A : Matrix (Fin g) (Fin g) ℝ := (τ b₀).map Complex.im with hAdef
  have hAu : IsUnit A.det := isUnit_iff_ne_zero.2 (hs b₀ hb₀).2.det_pos.ne'
  obtain ⟨c, hc, hrow⟩ := exists_entry_mulVec_ge A hAu
  set η : ℝ := c / (2 * ((g : ℝ) + 1)) with hηdef
  have hη : 0 < η := by positivity
  have hev : ∀ᶠ b in nhds b₀, b ∈ U ∧ ∀ k i, |(τ b k i).im - A k i| < η := by
    have hall : ∀ᶠ b in nhds b₀, ∀ k i, |(τ b k i).im - A k i| < η := by
      refine Filter.eventually_all.2 fun k => Filter.eventually_all.2 fun i => ?_
      have hcont : ContinuousAt (fun b => (τ b k i).im) b₀ :=
        Complex.continuous_im.continuousAt.comp
          ((hd k i).continuousOn.continuousAt (hU.mem_nhds hb₀))
      filter_upwards [hcont.preimage_mem_nhds (Metric.ball_mem_nhds ((τ b₀ k i).im) hη)]
        with b hb
      rw [Set.mem_preimage, Metric.mem_ball, Real.dist_eq] at hb
      simpa [hAdef] using hb
    filter_upwards [hU.mem_nhds hb₀, hall] with b h1 h2 using ⟨h1, h2⟩
  obtain ⟨ρ, hρ, hball⟩ := Metric.eventually_nhds_iff.1 hev
  have hcb : ∀ b ∈ Metric.closedBall b₀ (ρ / 2),
      b ∈ U ∧ ∀ k i, |(τ b k i).im - A k i| < η := fun b hb =>
    hball (lt_of_le_of_lt (Metric.mem_closedBall.1 hb) (by linarith))
  have hpi := Real.pi_pos
  refine ⟨ρ / 2, by positivity, fun b hb => (hcb b hb).1, 1 - Real.exp (-(2 * π * (c / 2))),
    sub_pos.2 ((Real.exp_lt_exp.2 (by nlinarith : -(2 * π * (c / 2)) < 0)).trans_eq Real.exp_zero), fun n hn => ?_⟩
  set v : Fin g → ℝ := fun i => (n i : ℝ) with hvdef
  have hv0 : v ≠ 0 := fun h => hn (funext fun i => by
    have := congrFun h i
    simpa [hvdef] using this)
  have hv1 : 1 ≤ ‖v‖ := by
    obtain ⟨j, hj⟩ := Function.ne_iff.1 hn
    have h1 : (1 : ℝ) ≤ |v j| := by
      simp only [hvdef]
      rw [← Int.cast_abs]
      exact_mod_cast Int.one_le_abs hj
    exact h1.trans ((Real.norm_eq_abs (v j)).symm ▸ norm_le_pi_norm v j)
  obtain ⟨k, hk⟩ := hrow v hv0
  refine ⟨k, fun b hb => ?_⟩
  have hbd := (hcb b hb).2 k
  refine le_norm_ex_sub_one n _ (by positivity) ?_
  rw [per_single_inl]
  change c / 2 ≤ |∑ i, v i * (τ b k i).im|
  have hsplit : ∑ i, v i * (τ b k i).im
      = (A *ᵥ v) k + ∑ i, v i * ((τ b k i).im - A k i) := by
    simp only [mulVec, dotProduct, mul_sub, Finset.sum_sub_distrib]
    rw [Finset.sum_congr rfl fun x _ => mul_comm (A k x) (v x)]
    ring
  have herr : |∑ i, v i * ((τ b k i).im - A k i)| ≤ c / 2 * ‖v‖ := by
    calc |∑ i, v i * ((τ b k i).im - A k i)|
        ≤ ∑ i, |v i * ((τ b k i).im - A k i)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _i : Fin g, ‖v‖ * η := by
          refine Finset.sum_le_sum fun i _ => ?_
          rw [abs_mul]
          exact mul_le_mul ((Real.norm_eq_abs (v i)).symm ▸ norm_le_pi_norm v i) (hbd i).le
            (abs_nonneg _) (norm_nonneg _)
      _ = (g : ℝ) * (‖v‖ * η) := by simp
      _ ≤ c / 2 * ‖v‖ := by
          rw [hηdef]
          have hg : (0 : ℝ) ≤ g := Nat.cast_nonneg g
          have hv := norm_nonneg v
          rw [show (g : ℝ) * (‖v‖ * (c / (2 * ((g : ℝ) + 1))))
              = c / 2 * ‖v‖ * ((g : ℝ) / ((g : ℝ) + 1)) by field_simp]
          have : (g : ℝ) / ((g : ℝ) + 1) ≤ 1 := by
            rw [div_le_one (by positivity)]; linarith
          have h0 : 0 ≤ c / 2 * ‖v‖ := by positivity
          nlinarith
  rw [hsplit]
  have h3 : |(A *ᵥ v) k| - |∑ i, v i * ((τ b k i).im - A k i)|
      ≤ |(A *ᵥ v) k + ∑ i, v i * ((τ b k i).im - A k i)| := by
    have := abs_add_le ((A *ᵥ v) k + ∑ i, v i * ((τ b k i).im - A k i))
      (-∑ i, v i * ((τ b k i).im - A k i))
    rw [add_neg_cancel_right, abs_neg] at this
    linarith
  nlinarith

end GlobalTheory.TauPeriod
