import Mathlib
import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.AffineCharacterGenerators.Generators
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HasSumTaylorOfExpBounds

open MvPolynomial Filter Topology PositivityTheory.Rg.Fx
open scoped ContDiff

theorem UpperTheory.ConvolutionTheory.FX.taylor_smooth :
    ∀ (ι : Type) [Fintype ι] (c : (ι → ℝ) → ℂ), ContDiff ℝ ∞ c → ∀ (H v : ι → ℝ) (M C : ℝ), (∀ (k : ℕ) (t : ℝ), t ∈ Set.Icc (0 : ℝ) 1 → ‖iteratedFDeriv ℝ k c (H + t • v) (fun _ => v)‖ ≤ M * C ^ k) → HasSum (fun k : ℕ => (k.factorial : ℂ)⁻¹ * iteratedFDeriv ℝ k c H (fun _ => v)) (c (H + v)) := by
  intro ι _ c hc' H h M A0 hb
  set L : ℝ →L[ℝ] (ι → ℝ) := ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) h with hL
  have hLt : ∀ t : ℝ, L t = t • h := fun t => by simp [hL]
  set cH : (ι → ℝ) → ℂ := fun z => c (H + z) with hcH
  have hcH' : ContDiff ℝ ∞ cH := hc'.comp (contDiff_const.add contDiff_id)
  set g : ℝ → ℂ := cH ∘ L with hg
  have hgs : ContDiff ℝ ∞ g := hcH'.comp L.contDiff
  have key : ∀ (j : ℕ) (t : ℝ),
      iteratedDeriv j g t = iteratedFDeriv ℝ j c (H + t • h) (fun _ => h) := by
    intro j t
    rw [iteratedDeriv_eq_iteratedFDeriv, hg,
      L.iteratedFDeriv_comp_right hcH' t (by exact_mod_cast le_top),
      ContinuousMultilinearMap.compContinuousLinearMap_apply, hcH,
      iteratedFDeriv_comp_add_left, hLt]
    simp [hLt]
  set A : ℝ := |A0| with hA
  have hA0 : 0 ≤ A := abs_nonneg _
  have bnd : ∀ (k : ℕ) (t : ℝ), t ∈ Set.Icc (0 : ℝ) 1 →
      ‖iteratedDeriv k g t‖ ≤ |M| * A ^ k := by
    intro k t ht
    rw [key]
    refine (hb k t ht).trans ?_
    calc M * A0 ^ k ≤ |M * A0 ^ k| := le_abs_self _
      _ = |M| * A ^ k := by rw [abs_mul, abs_pow]
  have hD : ∀ k : ℕ, iteratedFDeriv ℝ k c H (fun _ => h) = iteratedDeriv k g 0 := by
    intro k
    rw [key]
    simp
  have hsum : Summable
      (fun k : ℕ => ((Nat.factorial k : ℂ))⁻¹ * iteratedFDeriv ℝ k c H (fun _ => h)) := by
    have hs0 : Summable (fun k : ℕ => |M| * (A ^ k / (Nat.factorial k : ℝ))) :=
      (Real.summable_pow_div_factorial A).mul_left _
    refine Summable.of_norm_bounded hs0 ?_
    intro k
    rw [norm_mul, hD, norm_inv, Complex.norm_natCast]
    have := bnd k 0 (by simp)
    have hf : (0 : ℝ) ≤ ((Nat.factorial k : ℝ))⁻¹ := by positivity
    calc ((Nat.factorial k : ℝ))⁻¹ * ‖iteratedDeriv k g 0‖
        ≤ ((Nat.factorial k : ℝ))⁻¹ * (|M| * A ^ k) := mul_le_mul_of_nonneg_left this hf
      _ = |M| * (A ^ k / (Nat.factorial k : ℝ)) := by ring
  have htay : ∀ m : ℕ, taylorWithinEval g m (Set.Icc 0 1) 0 1 =
      ∑ k ∈ Finset.range (m + 1),
        ((Nat.factorial k : ℂ))⁻¹ * iteratedFDeriv ℝ k c H (fun _ => h) := by
    intro m
    rw [taylor_within_apply]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hD, iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Icc zero_lt_one)
      ((hgs.of_le (by exact_mod_cast le_top)).contDiffAt) (by simp)]
    simp [Complex.real_smul]
  have hrem : ∀ m : ℕ, ‖g 1 - taylorWithinEval g m (Set.Icc 0 1) 0 1‖ ≤
      |M| * A * (A ^ m / (Nat.factorial m : ℝ)) := by
    intro m
    have h1 := taylor_mean_remainder_bound (f := g) (a := 0) (b := 1) (x := 1) (n := m)
      (C := |M| * A ^ (m + 1)) zero_le_one
      ((hgs.of_le (by exact_mod_cast le_top)).contDiffOn) (by simp) (by
        intro y hy
        rw [iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Icc zero_lt_one)
          ((hgs.of_le (by exact_mod_cast le_top)).contDiffAt) hy]
        exact bnd _ y hy)
    refine h1.trans (le_of_eq ?_)
    simp only [sub_zero, one_pow, mul_one]
    ring
  have hlim : Tendsto (fun m : ℕ => taylorWithinEval g m (Set.Icc 0 1) 0 1) atTop (𝓝 (g 1)) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    have h0 : Tendsto (fun m : ℕ => |M| * A * (A ^ m / (Nat.factorial m : ℝ)))
        atTop (𝓝 0) := by
      simpa using (FloorSemiring.tendsto_pow_div_factorial_atTop A).const_mul (|M| * A)
    refine squeeze_zero (fun _ => norm_nonneg _) (fun m => ?_) h0
    rw [norm_sub_rev]
    exact hrem m
  have hg1 : g 1 = c (H + h) := by simp [hg, hcH, hLt]
  rw [← hg1, hsum.hasSum_iff_tendsto_nat, ← tendsto_add_atTop_iff_nat 1]
  simpa only [htay] using hlim
