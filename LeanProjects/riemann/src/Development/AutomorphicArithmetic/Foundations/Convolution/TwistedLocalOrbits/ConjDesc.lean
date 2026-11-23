import Development.AutomorphicArithmetic.Foundations.Convolution.HermitianDescent.ConjSep
import Development.AutomorphicArithmetic.Foundations.Convolution.TwistedLocalOrbits.Match

open MeasureTheory ValuativeRel GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets PositivityTheory.Rg.Tf.Loc UpperTheory.ConvolutionTheory.Loc

theorem UpperTheory.ConvolutionTheory.Loc.conjDesc :
    ∀ (k E : Type) [Field k] [Field E] [Algebra k E] (n : ℕ) (γ γ' : GL (Fin n) k), IsRegSemisimple γ →
      (∃ h : GL (Fin n) E, incl γ' = h * incl γ * h⁻¹) → ∃ y : GL (Fin n) k, γ' = y * γ * y⁻¹ := by
  intro k E _ _ _ n γ γ' hγ ⟨h, hh⟩
  have hc : (γ' : Matrix (Fin n) (Fin n) k).charpoly = (γ : Matrix (Fin n) (Fin n) k).charpoly := by
    apply Polynomial.map_injective (algebraMap k E) (algebraMap k E).injective
    rw [← Matrix.charpoly_map, ← Matrix.charpoly_map]
    have e := congrArg (fun g : GL (Fin n) E => (g : Matrix (Fin n) (Fin n) E).charpoly) hh
    simp only [Units.val_mul, Matrix.coe_units_inv, Matrix.charpoly_units_conj] at e
    exact e
  obtain ⟨x, hx⟩ := (UpperTheory.ConvolutionTheory.D.conjSep k k n _ hγ).1 _ hc
  refine ⟨x⁻¹, ?_⟩
  have : γ * x = x * γ' := Units.ext hx
  rw [inv_inv, mul_assoc, this, inv_mul_cancel_left]
