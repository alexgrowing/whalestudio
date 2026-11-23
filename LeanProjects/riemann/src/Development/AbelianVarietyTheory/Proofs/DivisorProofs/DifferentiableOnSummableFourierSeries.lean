import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.SiegelReframe
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SummableExpNegL1Norm
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.DifferentiableOnOfTendstoLocallyUniformlyOn
open Matrix MeasureTheory GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe GlobalTheory.TauPeriod Complex
open scoped Real ContDiff

noncomputable section

theorem GlobalTheory.TauPeriod.differentiableOn_tsum_coeff_mul_ex : ∀ {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E] {g : ℕ} {V : Set E} (d : (Fin g → ℤ) → E → ℂ), IsOpen V → (∀ n, DifferentiableOn ℂ (d n) V) → (∀ K ⊆ V, IsCompact K → ∀ R : ℝ, 0 ≤ R → ∃ M : ℝ, ∀ n, ∀ b ∈ K, ‖d n b‖ ≤ M * Real.exp (-(2 * π * R) * l1 n)) → DifferentiableOn ℂ (fun P : Pt E g => ∑' n, d n P.1 * ex n P.2) (cov V g) ∧ ∀ P : Pt E g, P.1 ∈ V → Summable (fun n => d n P.1 * ex n P.2) := by
  intro E _ _ _ g V d hV hd hdec
  haveI : ProperSpace E := FiniteDimensional.proper ℂ E
  have key : ∀ P : Pt E g, P.1 ∈ V → ∃ t ∈ nhds P, ∃ u : (Fin g → ℤ) → ℝ, Summable u ∧
      ∀ n, ∀ Q ∈ t, ‖d n Q.1 * ex n Q.2‖ ≤ u n := by
    intro P hP
    obtain ⟨K, ⟨hKx, hK⟩, hKV⟩ := (compact_basis_nhds P.1).mem_iff.mp (hV.mem_nhds hP)
    set Y : ℝ := ‖P.2‖ + 1 with hY
    have hY0 : 0 ≤ Y := by positivity
    obtain ⟨M, hM⟩ := hdec K hKV hK (Y + 1) (by positivity)
    refine ⟨K ×ˢ Metric.ball P.2 1, prod_mem_nhds hKx (Metric.ball_mem_nhds _ one_pos),
      fun n => M * Real.exp (-(2 * π) * l1 n),
      (summable_exp_neg_l1Norm (by positivity : (0:ℝ) < 2 * π)).mul_left M, ?_⟩
    rintro n ⟨b, w⟩ ⟨hb, hw⟩
    have hwn : ‖w‖ ≤ Y := by
      have h1 := norm_sub_norm_le w P.2
      have h2 : ‖w - P.2‖ < 1 := by simpa [dist_eq_norm] using hw
      rw [hY]; linarith
    have hex : ‖ex n w‖ ≤ Real.exp (2 * π * Y * l1 n) := by
      rw [norm_ex]
      apply Real.exp_le_exp.2
      have hi : ∀ i, -((n i : ℝ) * (w i).im) ≤ |(n i : ℝ)| * Y := fun i => by
        have h1 : |(w i).im| ≤ Y := (abs_im_le_norm _).trans ((norm_le_pi_norm w i).trans hwn)
        calc -((n i : ℝ) * (w i).im) ≤ |(n i : ℝ) * (w i).im| := neg_le_abs _
          _ = |(n i : ℝ)| * |(w i).im| := abs_mul _ _
          _ ≤ |(n i : ℝ)| * Y := mul_le_mul_of_nonneg_left h1 (abs_nonneg _)
      have hs : -∑ i, (n i : ℝ) * (w i).im ≤ Y * l1 n := by
        rw [← Finset.sum_neg_distrib, l1, Finset.mul_sum]
        exact Finset.sum_le_sum fun i _ => (hi i).trans (le_of_eq (mul_comm _ _))
      have hπ : 0 ≤ 2 * π := by positivity
      nlinarith [mul_le_mul_of_nonneg_left hs hπ]
    have hdb := hM n b hb
    calc ‖d n (b, w).1 * ex n (b, w).2‖ = ‖d n b‖ * ‖ex n w‖ := norm_mul _ _
      _ ≤ (M * Real.exp (-(2 * π * (Y + 1)) * l1 n)) * Real.exp (2 * π * Y * l1 n) :=
          mul_le_mul hdb hex (norm_nonneg _) ((norm_nonneg _).trans hdb)
      _ = M * Real.exp (-(2 * π) * l1 n) := by
          rw [mul_assoc, ← Real.exp_add]; congr 2; ring
  have hcov : ∀ P : Pt E g, P ∈ cov V g → P.1 ∈ V := fun P hP => (Set.mem_prod.1 hP).1
  refine ⟨GlobalTheory.SCV.differentiableOn_tsum_of_locally_normal (hV.prod isOpen_univ) (fun n => ?_)
    (fun P hP => key P (hcov P hP)), fun P hP => ?_⟩
  · exact ((hd n).comp differentiableOn_fst (fun P hP => hcov P hP)).mul
      ((differentiable_ex n).comp differentiable_snd).differentiableOn
  · obtain ⟨t, ht, u, hu, h⟩ := key P hP
    exact Summable.of_norm_bounded hu (fun n => h n P (mem_of_mem_nhds ht))
