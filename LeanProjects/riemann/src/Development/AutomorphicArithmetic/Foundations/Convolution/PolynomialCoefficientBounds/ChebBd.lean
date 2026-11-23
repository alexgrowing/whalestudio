import Mathlib
import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.AffineCharacterGenerators.Generators
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HasSumTaylorOfExpBounds
import Development.AutomorphicArithmetic.Foundations.Convolution.PolynomialCoefficientBounds.ChebClosed

open MvPolynomial Filter Topology PositivityTheory.Rg.Fx
open scoped ContDiff

theorem UpperTheory.ConvolutionTheory.FX.cheb_bound :
    ∀ (η : ℝ) (m : ℕ), 0 < η → η ≤ 1 → (∀ a ∈ Set.Icc 0 η, |cheb η m a| ≤ 1) ∧ (∀ a ∈ Set.Icc (0 : ℝ) 1, |cheb η m a| ≤ (4 / η) ^ m) ∧ ∃ q : Polynomial ℝ, q.natDegree ≤ m ∧ ∀ a, q.eval a = cheb η m a := by
  intro η m hη hη1
  have hA : ∀ a ∈ Set.Icc 0 η, |cheb η m a| ≤ 1 := by
    intro a ha
    unfold cheb
    refine (UpperTheory.ConvolutionTheory.FX.cheb_facts m _).1 ?_
    have h0 : 0 ≤ 2 * a / η := div_nonneg (by linarith [ha.1]) hη.le
    have h2 : 2 * a / η ≤ 2 := by
      rw [div_le_iff₀ hη]; linarith [ha.2]
    rw [abs_le]; constructor <;> linarith
  refine ⟨hA, ?_, ?_⟩
  · intro a ha
    by_cases h : a ≤ η
    · refine (hA a ⟨ha.1, h⟩).trans (one_le_pow₀ ?_)
      rw [le_div_iff₀ hη]; linarith
    · have h : η < a := lt_of_not_ge h
      have h2 : 2 ≤ 2 * a / η := by
        rw [le_div_iff₀ hη]; linarith
      have h3 : 2 * (2 * a / η) ≤ 4 / η := by
        rw [← mul_div_assoc]
        exact div_le_div_of_nonneg_right (by linarith [ha.2]) hη.le
      unfold cheb
      refine ((UpperTheory.ConvolutionTheory.FX.cheb_facts m _).2 (by linarith)).2.trans ?_
      exact pow_le_pow_left₀ (by linarith) (by linarith) m
  · refine ⟨(Polynomial.Chebyshev.T ℝ (m : ℤ)).comp
      (Polynomial.C (2 / η) * Polynomial.X + Polynomial.C (-1)), ?_, ?_⟩
    · refine Polynomial.natDegree_comp_le.trans ?_
      rw [Polynomial.Chebyshev.natDegree_T, Int.natAbs_natCast]
      calc m * _ ≤ m * 1 := Nat.mul_le_mul_left m Polynomial.natDegree_linear_le
        _ = m := Nat.mul_one m
    · intro a
      unfold cheb
      rw [Polynomial.eval_comp]
      congr 1
      simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]
      ring
