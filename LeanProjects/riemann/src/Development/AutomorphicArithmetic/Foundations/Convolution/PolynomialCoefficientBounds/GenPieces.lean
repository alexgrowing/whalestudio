import Mathlib
import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.AffineCharacterGenerators.Generators
import Development.AutomorphicArithmetic.Foundations.Convolution.PolynomialCoefficientBounds.CoeffL1NormNonneg
import Development.AutomorphicArithmetic.Foundations.Convolution.PolynomialCoefficientBounds.PieceHom
import Development.AutomorphicArithmetic.Foundations.Convolution.PolynomialCoefficientBounds.IntMvPolynomialCoeffAbsSumAddLe
import Development.AutomorphicArithmetic.Foundations.Convolution.PolynomialCoefficientBounds.AevalSingleZero

open MvPolynomial Filter Topology PositivityTheory.Rg.Fx

theorem UpperTheory.ConvolutionTheory.FX.gen_pieces :
    ∀ (τ : Type) [Fintype τ] [DecidableEq τ] (n : ℕ) (f : EP (τ × Fin n)), (∀ w : τ → Equiv.Perm (Fin n), ren (fun ti : τ × Fin n => (ti.1, w ti.1 ti.2)) f = f) → ∃ (K : ℝ) (G : ℕ → MvPolynomial (τ × Fin n) ℂ), ∀ k, aeval blockE (G k) = piece k f ∧ (G k).totalDegree ≤ k ∧ l1 (G k) ≤ K ^ (k + 1) / k.factorial := by
  intro τ _ _ n f hf
  have hgen : Generators := UpperTheory.ConvolutionTheory.FX.generators0
  obtain ⟨K₁, hK₁⟩ := hgen τ n
  obtain ⟨K₂, hK₂⟩ := UpperTheory.ConvolutionTheory.FX.piece_size (τ × Fin n) f
  have h : ∀ k, ∃ G : MvPolynomial (τ × Fin n) ℂ, aeval blockE G = piece k f ∧ G.totalDegree ≤ k ∧
      l1 G ≤ K₁ ^ (k + 1) * l1 (piece k f) := fun k =>
    hK₁ k (piece k f) (UpperTheory.ConvolutionTheory.FX.piece_hom _ f k).totalDegree_le
      (fun w => by rw [← UpperTheory.ConvolutionTheory.FX.piece_ren, hf w])
  choose G hG using h
  refine ⟨|K₁| * K₂, G, fun k => ⟨(hG k).1, (hG k).2.1, ?_⟩⟩
  have h0 : 0 ≤ l1 (piece k f) := Finset.sum_nonneg fun _ _ => norm_nonneg _
  calc l1 (G k) ≤ K₁ ^ (k + 1) * l1 (piece k f) := (hG k).2.2
    _ ≤ |K₁| ^ (k + 1) * l1 (piece k f) := by
        refine mul_le_mul_of_nonneg_right ?_ h0
        rw [← abs_pow]; exact le_abs_self _
    _ ≤ |K₁| ^ (k + 1) * (K₂ ^ (k + 1) / k.factorial) :=
        mul_le_mul_of_nonneg_left (hK₂ k) (by positivity)
    _ = (|K₁| * K₂) ^ (k + 1) / k.factorial := by rw [mul_pow]; ring
