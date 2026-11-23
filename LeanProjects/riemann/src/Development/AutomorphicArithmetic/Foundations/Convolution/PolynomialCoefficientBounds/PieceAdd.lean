import Mathlib
import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.AffineCharacterGenerators.Generators

open MvPolynomial Filter Topology PositivityTheory.Rg.Fx

theorem UpperTheory.ConvolutionTheory.FX.piece_add :
    ∀ (ι : Type) [Fintype ι] (k : ℕ), (∀ f g : EP ι, piece k (f + g) = piece k f + piece k g) ∧ piece k (0 : EP ι) = 0 ∧ ∀ (v : ι → ℝ) (p : MvPolynomial ι ℂ), piece k (AddMonoidAlgebra.single v p : EP ι) = ∑ b ∈ Finset.range (k + 1), homogeneousComponent (k - b) p * (C ((b.factorial : ℂ)⁻¹) * lin v ^ b) := by
  intro ι _ k
  refine ⟨fun f g => ?_, ?_, fun v p => ?_⟩
  · unfold piece
    rw [AddMonoidAlgebra.coeff_add, Finsupp.sum_add_index']
    · intro a; simp
    · intro a b c; simp [add_mul, Finset.sum_add_distrib]
  · unfold piece
    simp
  · unfold piece
    rw [AddMonoidAlgebra.coeff_single, Finsupp.sum_single_index]
    simp
