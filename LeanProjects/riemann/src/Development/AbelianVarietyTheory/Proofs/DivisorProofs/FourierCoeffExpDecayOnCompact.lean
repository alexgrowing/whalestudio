import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.SiegelReframe
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SummableExpNegL1Norm
open Matrix MeasureTheory GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe GlobalTheory.TauPeriod Complex
open scoped Real ContDiff

namespace GlobalTheory.TauPeriod

theorem fibreCoeff_decay : ∀ {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E] {g : ℕ} {U : Set E} (a : Pt E g → ℂ), IsOpen U → DifferentiableOn ℂ a (cov U g) → (∀ j : Fin g, ∀ P ∈ cov U g, a (P.1, P.2 + Pi.single j 1) = a P) → ∀ K ⊆ U, IsCompact K → ∀ R : ℝ, 0 ≤ R → ∃ M : ℝ, ∀ n : Fin g → ℤ, ∀ b ∈ K, ‖cf (fun z => a (b, z)) n‖ ≤ M * Real.exp (-(2 * π * R) * l1 n) := by
  intro E _ _ _ g U a hU ha hper K hKU hK R hR
  have hcovopen : IsOpen (cov U g) := hU.prod isOpen_univ
  have hcont : ContinuousOn a (cov U g) := ha.continuousOn
  have hKS : IsCompact (K ×ˢ Metric.closedBall (0 : Fin g → ℂ) (1 + R)) :=
    hK.prod (isCompact_closedBall _ _)
  have hsub : K ×ˢ Metric.closedBall (0 : Fin g → ℂ) (1 + R) ⊆ cov U g :=
    fun P hP => ⟨hKU hP.1, Set.mem_univ _⟩
  obtain ⟨C, hC⟩ := hKS.exists_bound_of_continuousOn (hcont.mono hsub)
  refine ⟨max C 0, fun n b hb => ?_⟩
  set f : (Fin g → ℂ) → ℂ := fun z => a (b, z) with hf_def
  have hfd : Differentiable ℂ f := fun z => by
    have hP : (b, z) ∈ cov U g := ⟨hKU hb, Set.mem_univ _⟩
    have h1 : DifferentiableAt ℂ a (b, z) := ha.differentiableAt (hcovopen.mem_nhds hP)
    exact h1.comp z ((differentiableAt_const b).prodMk differentiableAt_id)
  have hfp : ∀ (i : Fin g) z, f (z + Pi.single i 1) = f z := fun i z =>
    hper i (b, z) ⟨hKU hb, Set.mem_univ _⟩
  have hs : ∀ i, (n i : ℝ) * ((Int.sign (n i) : ℤ) : ℝ) = |(n i : ℝ)| ∧
      |((Int.sign (n i) : ℤ) : ℝ)| ≤ 1 := by
    intro i
    rcases lt_trichotomy (n i) 0 with h | h | h
    · have h' : (n i : ℝ) < 0 := by exact_mod_cast h
      simp [Int.sign_eq_neg_one_of_neg h, abs_of_neg h']
    · simp [h]
    · have h' : (0 : ℝ) < n i := by exact_mod_cast h
      simp [Int.sign_eq_one_of_pos h, abs_of_pos h']
  set w : Fin g → ℂ := fun i => Complex.I * (((-(R * ((Int.sign (n i) : ℤ) : ℝ))) : ℝ) : ℂ)
    with hw
  have htr := cf_translate f hfd hfp n w
  have hsum : ∑ i, (n i : ℝ) * (w i).im = -R * l1 n := by
    rw [l1, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    have him : (w i).im = -(R * ((Int.sign (n i) : ℤ) : ℝ)) := by simp [hw]
    rw [him, ← (hs i).1]
    ring
  have hex : ‖ex n w‖ = Real.exp (2 * π * R * l1 n) := by
    rw [norm_ex, hsum]
    congr 1
    ring
  have hvol : volume (Set.Icc (0 : Fin g → ℝ) 1) = 1 := by simp [Real.volume_Icc_pi]
  have hbound : ‖cf (fun z => f (z + w)) n‖ ≤ C := by
    unfold cf
    have hvr : (volume : Measure (Fin g → ℝ)).real (Set.Icc (0 : Fin g → ℝ) 1) = 1 := by
      simp [Measure.real, hvol]
    calc _ ≤ C * (volume : Measure (Fin g → ℝ)).real (Set.Icc (0 : Fin g → ℝ) 1) :=
          norm_setIntegral_le_of_norm_le_const (by rw [hvol]; exact ENNReal.one_lt_top)
            (fun x hx => ?_)
      _ = C := by rw [hvr, mul_one]
    rw [norm_mul]
    have h1 : ‖cexp (-(2 * π * I) * ∑ i, (n i : ℂ) * (x i : ℂ))‖ = 1 := by
      rw [Complex.norm_exp]
      have : (-(2 * π * I) * ∑ i, (n i : ℂ) * (x i : ℂ)).re = 0 := by
        have e : ∑ i, (n i : ℂ) * (x i : ℂ) = ((∑ i, (n i : ℝ) * x i : ℝ) : ℂ) := by
          push_cast; rfl
        rw [e]; simp
      rw [this, Real.exp_zero]
    rw [h1, mul_one]
    apply hC
    refine ⟨hb, ?_⟩
    rw [Metric.mem_closedBall, dist_zero_right]
    refine (pi_norm_le_iff_of_nonneg (by linarith)).2 fun i => ?_
    have hx1 : ‖((x i : ℝ) : ℂ)‖ ≤ 1 := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_le]
      constructor
      · have h0 : (0 : ℝ) ≤ x i := hx.1 i
        linarith
      · exact hx.2 i
    have hw1 : ‖w i‖ ≤ R := by
      simp only [hw, norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_neg, abs_mul, abs_of_nonneg hR]
      calc R * |((Int.sign (n i) : ℤ) : ℝ)| ≤ R * 1 := mul_le_mul_of_nonneg_left (hs i).2 hR
        _ = R := mul_one R
    calc ‖((fun i => ((x i : ℝ) : ℂ)) + w) i‖ = ‖((x i : ℝ) : ℂ) + w i‖ := rfl
      _ ≤ ‖((x i : ℝ) : ℂ)‖ + ‖w i‖ := norm_add_le _ _
      _ ≤ 1 + R := add_le_add hx1 hw1
  have hmain : ‖cf f n‖ * Real.exp (2 * π * R * l1 n) ≤ C := by
    rw [mul_comm, ← hex, ← norm_mul, ← htr]
    exact hbound
  have e : Real.exp (2 * π * R * l1 n) * Real.exp (-(2 * π * R) * l1 n) = 1 := by
    rw [← Real.exp_add, show 2 * π * R * l1 n + -(2 * π * R) * l1 n = 0 by ring, Real.exp_zero]
  calc ‖cf f n‖ = (‖cf f n‖ * Real.exp (2 * π * R * l1 n)) * Real.exp (-(2 * π * R) * l1 n) := by
        rw [mul_assoc, e, mul_one]
    _ ≤ max C 0 * Real.exp (-(2 * π * R) * l1 n) :=
        mul_le_mul_of_nonneg_right (hmain.trans (le_max_left _ _)) (Real.exp_pos _).le

end GlobalTheory.TauPeriod
