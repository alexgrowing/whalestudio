import Development.AutomorphicArithmetic.Foundations.Convolution.NormCharacterPowers.OrderAsym
import Development.WeilBound.RepresentationTheoryGL.JacquetShalikaBounds.AbsoluteRigidity.AbsRigClosed
import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.AnalyticSeries.AnalyticAtTsum

open UpperTheory.ConvolutionTheory.R

open PositivityTheory.RgJS PositivityTheory.RgJS.Common0Aux in
theorem UpperTheory.ConvolutionTheory.R.zeroExp :
    ZeroExp := by
  classical
  intro W q X d A hS ι _ x hw hsm
  by_contra hne
  push Not at hne
  obtain ⟨i₁, hi₁⟩ := hne
  have hq := hS.primes.two
  have hC := UpperTheory.ConvolutionTheory.Rs.conv1 W q X d A hS
  obtain ⟨i₀, -, hi₀⟩ := Finset.exists_min_image Finset.univ (fun i => (x i).2) ⟨i₁, Finset.mem_univ _⟩
  set m : ℝ := (x i₀).2 with hm
  have ht : ∀ i, m ≤ (x i).2 := fun i => hi₀ i (Finset.mem_univ _)
  have hm0 : m < 0 := by
    by_contra h
    push Not at h
    have h1 := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ =>
      mul_nonneg (Nat.cast_nonneg (d (x i).1)) (h.trans (ht i)))).1 hw i₁ (Finset.mem_univ _)
    rcases mul_eq_zero.1 h1 with h2 | h2
    · have := hS.pos (x i₁).1
      have h3 : d (x i₁).1 = 0 := by exact_mod_cast h2
      omega
    · exact hi₁ h2
  set α : W → (Σ i, Fin (d (x i).1)) → ℂ :=
    fun w a => A (x a.1).1 w a.2 * (q w : ℂ) ^ (-((x a.1).2 : ℂ)) with hα
  have hxx : ∀ (σ : ℝ) (p : W × ℕ),
      ∑ i, ∑ j, lterm q (A (x i).1) (A (x j).1) (((σ + (x i).2 + (x j).2 : ℝ)) : ℂ) p = lterm q α α σ p := fun σ p => by
    rw [sum_lterm q hq A x x σ p]
    simp only [lterm, Pw, hα, Fintype.sum_sigma]
  obtain ⟨τ, hτ, -, hτle⟩ := exists_pos_le (fun i => (x i).2 - m) (fun i => (x i).2 ≠ m)
    (fun i hi => sub_pos.2 (lt_of_le_of_ne (ht i) (Ne.symm hi)))
  choose M hM using fun i i' : ι => (hC (x i).1 (x i').1).2 (1 + τ) (by linarith)
  have : Nonempty {i // (x i).2 = m} := ⟨⟨i₀, rfl⟩⟩
  refine UpperTheory.ConvolutionTheory.Rs.unb W q X d A hS {i // (x i).2 = m} (fun i => (x i.1).1)
    ⟨(∑' p, ‖lterm q α α ((1 - 2 * m : ℝ) : ℂ) p‖) + ∑ i, ∑ i', |M i i'|, fun σ hσ1 hσ2 => ?_⟩
  have hs : ∀ i j, Summable fun p => lterm q (A (x i).1) (A (x j).1) (((σ - 2 * m + (x i).2 + (x j).2 : ℝ)) : ℂ) p :=
    fun i j => ((hC _ _).1 _ (by linarith [ht i, ht j])).of_norm
  have hform : ∑ i : {i // (x i).2 = m}, ∑ j : {i // (x i).2 = m}, ∑' p, lterm q (A (x i.1).1) (A (x j.1).1) (σ : ℂ) p =
      ∑ i : {i // (x i).2 = m}, ∑ j : {i // (x i).2 = m},
        ∑' p, lterm q (A (x i.1).1) (A (x j.1).1) (((σ - 2 * m + (x i.1).2 + (x j.1).2 : ℝ)) : ℂ) p := by
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [i.2, j.2, show σ - 2 * m + m + m = σ by ring]
  have htot : ∑ i, ∑ j, ∑' p, lterm q (A (x i).1) (A (x j).1) (((σ - 2 * m + (x i).2 + (x j).2 : ℝ)) : ℂ) p =
      ∑' p, lterm q α α ((σ - 2 * m : ℝ) : ℂ) p := by
    calc ∑ i, ∑ j, ∑' p, lterm q (A (x i).1) (A (x j).1) (((σ - 2 * m + (x i).2 + (x j).2 : ℝ)) : ℂ) p
        = ∑ i, ∑' p, ∑ j, lterm q (A (x i).1) (A (x j).1) (((σ - 2 * m + (x i).2 + (x j).2 : ℝ)) : ℂ) p :=
          Finset.sum_congr rfl fun i _ => (Summable.tsum_finsetSum fun j _ => hs i j).symm
      _ = ∑' p, ∑ i, ∑ j, lterm q (A (x i).1) (A (x j).1) (((σ - 2 * m + (x i).2 + (x j).2 : ℝ)) : ℂ) p :=
          (Summable.tsum_finsetSum fun i _ => summable_sum (s := Finset.univ) fun j _ => hs i j).symm
      _ = _ := tsum_congr fun p => hxx _ p
  rw [hform, dsum_subtype (fun i => (x i).2 = m)
    (fun i j => ∑' p, lterm q (A (x i).1) (A (x j).1) (((σ - 2 * m + (x i).2 + (x j).2 : ℝ)) : ℂ) p)]
  set f : ι → ι → ℂ :=
    fun i j => ∑' p, lterm q (A (x i).1) (A (x j).1) (((σ - 2 * m + (x i).2 + (x j).2 : ℝ)) : ℂ) p with hf
  have hsplit : ∑ i, ∑ j, f i j = (∑ i, ∑ j, if (x i).2 = m ∧ (x j).2 = m then f i j else 0) +
      ∑ i, ∑ j, if (x i).2 = m ∧ (x j).2 = m then 0 else f i j := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    split_ifs <;> simp
  have hrest : ‖∑ i, ∑ j, if (x i).2 = m ∧ (x j).2 = m then (0 : ℂ) else f i j‖ ≤ ∑ i, ∑ i', |M i i'| := by
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => (norm_sum_le _ _).trans
      (Finset.sum_le_sum fun j _ => ?_))
    split_ifs with hij
    · simp
    · have hge : 1 + τ ≤ σ - 2 * m + (x i).2 + (x j).2 := by
        rcases not_and_or.1 hij with h | h
        · linarith [hτle i h, ht j]
        · linarith [hτle j h, ht i]
      exact (hM i j _ hge).trans (le_abs_self _)
  have hDle : ‖∑' p, lterm q α α ((σ - 2 * m : ℝ) : ℂ) p‖ ≤ ∑' p, ‖lterm q α α ((1 - 2 * m : ℝ) : ℂ) p‖ :=
    tsum_of_norm_bounded (hsm (1 - 2 * m) (by linarith)).hasSum fun p =>
      DiagonalEntryNormBounds.norm_lterm_anti q hq α α (by linarith) p
  have heq : (∑ i, ∑ j, if (x i).2 = m ∧ (x j).2 = m then f i j else 0) =
      (∑' p, lterm q α α ((σ - 2 * m : ℝ) : ℂ) p) -
        ∑ i, ∑ j, if (x i).2 = m ∧ (x j).2 = m then 0 else f i j := by
    rw [← htot, hsplit]
    ring
  rw [heq]
  exact (norm_sub_le _ _).trans (add_le_add hDle hrest)
