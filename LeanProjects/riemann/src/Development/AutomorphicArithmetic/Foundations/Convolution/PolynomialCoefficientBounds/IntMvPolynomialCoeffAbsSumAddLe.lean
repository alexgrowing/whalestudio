import Mathlib
import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.AffineCharacterGenerators.Generators
import Development.AutomorphicArithmetic.Foundations.Convolution.PolynomialCoefficientBounds.MatrixEntryAbsSumUnitaryLieCoordinatesSplit
import Development.AutomorphicArithmetic.Foundations.Convolution.PolynomialCoefficientBounds.PieceAdd

open MvPolynomial Filter Topology PositivityTheory.Rg.Fx

private theorem weightAbsEntrySum_nonneg {ι : Type} (p : MvPolynomial ι ℂ) : 0 ≤ l1 p := Finset.sum_nonneg fun _ _ => norm_nonneg _

private theorem intMvPolynomialCoeffAbsSum_add_le {ι : Type} (p q : MvPolynomial ι ℂ) : l1 (p + q) ≤ l1 p + l1 q := (UpperTheory.ConvolutionTheory.FX.coeffL1_submultiplicative_facts ι p q).1

private theorem intMvPolynomialCoeffAbsSum_mul_le {ι : Type} (p q : MvPolynomial ι ℂ) : l1 (p * q) ≤ l1 p * l1 q := (UpperTheory.ConvolutionTheory.FX.coeffL1_submultiplicative_facts ι p q).2.1

private theorem intMvPolynomialCoeffAbsSum_sum_le {ι κ : Type} (s : Finset κ) (f : κ → MvPolynomial ι ℂ) : l1 (∑ i ∈ s, f i) ≤ ∑ i ∈ s, l1 (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [l1]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact (intMvPolynomialCoeffAbsSum_add_le _ _).trans (by linarith)

private theorem intMvPolynomialCoeffAbsSum_pow_le {ι : Type} (p : MvPolynomial ι ℂ) (b : ℕ) : l1 (p ^ b) ≤ l1 p ^ b := by
  induction b with
  | zero =>
    have := (UpperTheory.ConvolutionTheory.FX.coeffL1_submultiplicative_facts ι 0 0).2.2.2.1 (0 : ι →₀ ℕ) 1
    simp only [monomial_zero', C_1, norm_one] at this
    simpa [l1] using this.le
  | succ b ih => rw [pow_succ, pow_succ]; exact (intMvPolynomialCoeffAbsSum_mul_le _ _).trans (mul_le_mul_of_nonneg_right ih (weightAbsEntrySum_nonneg _))

theorem UpperTheory.ConvolutionTheory.FX.piece_size :
    ∀ (ι : Type) [Fintype ι] (f : EP ι), ∃ K : ℝ, ∀ k, l1 (piece k f) ≤ K ^ (k + 1) / k.factorial := by
  intro ι _ f
  suffices h : ∃ K : ℝ, 0 ≤ K ∧ ∀ k, l1 (piece k f) ≤ K ^ (k + 1) / k.factorial from h.imp fun _ h => h.2
  induction f using AddMonoidAlgebra.induction_linear with
  | zero => exact ⟨0, le_rfl, fun k => by simp [(UpperTheory.ConvolutionTheory.FX.piece_add ι k).2.1, l1]⟩
  | add f g hf hg =>
    obtain ⟨K, hK, h⟩ := hf
    obtain ⟨K', hK', h'⟩ := hg
    refine ⟨K + K', by positivity, fun k => ?_⟩
    rw [(UpperTheory.ConvolutionTheory.FX.piece_add ι k).1]
    refine (intMvPolynomialCoeffAbsSum_add_le _ _).trans ((add_le_add (h k) (h' k)).trans ?_)
    rw [← add_div]
    gcongr
    exact pow_add_pow_le hK hK' (Nat.succ_ne_zero k)
  | single v p =>
    set D : ℝ := ((p.totalDegree.factorial : ℕ) : ℝ) with hDd
    set y := l1 (lin v)
    have hy : 0 ≤ y := weightAbsEntrySum_nonneg _
    have hp := weightAbsEntrySum_nonneg p
    have hD : 0 ≤ D := Nat.cast_nonneg _
    refine ⟨l1 p * D + (y + 1), by positivity, fun k => ?_⟩
    rw [(UpperTheory.ConvolutionTheory.FX.piece_add ι k).2.2]
    have hk : (0 : ℝ) < k.factorial := by exact_mod_cast k.factorial_pos
    have t : ∀ b ∈ Finset.range (k + 1), l1 (homogeneousComponent (k - b) p * (C ((b.factorial : ℂ)⁻¹) * lin v ^ b)) ≤
        l1 p * D / k.factorial * (y ^ b * 1 ^ (k - b) * k.choose b) := by
      intro b hb
      have hbk : b ≤ k := Nat.lt_succ_iff.1 (Finset.mem_range.1 hb)
      by_cases hd : p.totalDegree < k - b
      · rw [homogeneousComponent_eq_zero _ p hd, zero_mul]
        simp only [l1, support_zero, Finset.sum_empty]
        exact mul_nonneg (div_nonneg (mul_nonneg hp hD) hk.le) (by positivity)
      · have h1 : l1 (homogeneousComponent (k - b) p) ≤ l1 p := (UpperTheory.ConvolutionTheory.FX.coeffL1_submultiplicative_facts ι p p).2.2.2.2.1 _
        have h2 : l1 (C ((b.factorial : ℂ)⁻¹) * lin v ^ b) ≤ (b.factorial : ℝ)⁻¹ * y ^ b := by
          have e : l1 (C ((b.factorial : ℂ)⁻¹) * lin v ^ b) = ‖(b.factorial : ℂ)⁻¹‖ * l1 (lin v ^ b) :=
            (UpperTheory.ConvolutionTheory.FX.coeffL1_submultiplicative_facts ι (lin v ^ b) p).2.2.1 _
          rw [e, norm_inv, Complex.norm_natCast]
          exact mul_le_mul_of_nonneg_left (intMvPolynomialCoeffAbsSum_pow_le _ _) (by positivity)
        have h3 : ((k - b).factorial : ℝ) ≤ D := Nat.cast_le.2 (Nat.factorial_le (not_lt.1 hd))
        have h4 : (k.factorial : ℝ) = k.choose b * b.factorial * (k - b).factorial := by
          exact_mod_cast (Nat.choose_mul_factorial_mul_factorial hbk).symm
        have hb0 : (0 : ℝ) < b.factorial := by exact_mod_cast b.factorial_pos
        have hc0 : (0 : ℝ) < k.choose b := by exact_mod_cast Nat.choose_pos hbk
        have he0 : (0 : ℝ) < (k - b).factorial := by exact_mod_cast (k - b).factorial_pos
        refine (intMvPolynomialCoeffAbsSum_mul_le _ _).trans ((mul_le_mul h1 h2 (weightAbsEntrySum_nonneg _) hp).trans ?_)
        calc l1 p * ((b.factorial : ℝ)⁻¹ * y ^ b)
            = l1 p * (k - b).factorial / k.factorial * (y ^ b * 1 ^ (k - b) * k.choose b) := by
              rw [h4]; field_simp; simp
          _ ≤ _ := by gcongr
    refine (intMvPolynomialCoeffAbsSum_sum_le _ _).trans ((Finset.sum_le_sum t).trans ?_)
    rw [← Finset.mul_sum, ← add_pow, div_mul_eq_mul_div, pow_succ']
    have : 0 ≤ l1 p * D := mul_nonneg hp hD
    refine div_le_div_of_nonneg_right (mul_le_mul (by linarith) (pow_le_pow_left₀ (by linarith) (by linarith) k) (by positivity) (by linarith)) hk.le
