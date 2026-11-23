import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.SelmerRankBounds.EllipticityFromProductFormula
import Development.AutomorphicArithmetic.Foundations.Convolution.HermitianDescent.SeparableOfMap
import Development.AutomorphicArithmetic.Foundations.Convolution.HermitianDescent.ConjSep
import Development.AutomorphicArithmetic.Foundations.Convolution.HermitianDescent.GalField
open PositivityTheory.Rg.Tf.Geo

open PositivityTheory.Rg.Tf.Loc in
private theorem nm_eq_normGL {k E : Type} [Field k] [Field E] [Algebra k E] (σ : E ≃ₐ[k] E) (n q : ℕ)
    (d : GL (Fin n) E) : UpperTheory.ConvolutionTheory.D.nm σ q d = twNorm (sigmaGL σ) q d := by
  unfold UpperTheory.ConvolutionTheory.D.nm twNorm
  congr 1
  refine List.map_congr_left fun i _ => ?_
  rw [← sigmaGL_pow]
  rfl

open PositivityTheory.Rg.Tf.Loc in
theorem UpperTheory.ConvolutionTheory.G.nm_agrees_with_twisted_norm_sigmaGL :
    N2 := by
  intro k E _ _ _ _ _ _ σ hσ n
  refine ⟨?_, ?_⟩
  · intro δ δ' γ hγ h1 h2
    have hg := UpperTheory.ConvolutionTheory.D.galField k E σ hσ
    have e : ∀ d : GL (Fin n) E, UpperTheory.ConvolutionTheory.D.nm σ (Module.finrank k E) d = normGL σ d :=
      fun d => nm_eq_normGL σ n _ d
    have hsep : (UpperTheory.ConvolutionTheory.D.cp (UpperTheory.ConvolutionTheory.D.nm σ (Module.finrank k E) δ)).Separable := by
      rw [e, h1]
      have hm : UpperTheory.ConvolutionTheory.D.cp (incl γ : GL (Fin n) E) =
          ((γ : Matrix (Fin n) (Fin n) k).charpoly).map (algebraMap k E) := by
        rw [← Matrix.charpoly_map]
        rfl
      rw [hm]
      exact hγ.map
    obtain ⟨x, hx⟩ := UpperTheory.ConvolutionTheory.D.nmInj k E σ _ hg n δ δ' hsep (by rw [e, e, h1, h2])
    exact ⟨x, hx⟩
  · intro γ γ' hγ hc
    obtain ⟨x, hx⟩ := (UpperTheory.ConvolutionTheory.D.conjSep k k n (γ : Matrix (Fin n) (Fin n) k) hγ).1 γ' hc.symm
    have hx' : γ * x = x * γ' := Units.ext hx
    refine ⟨x, ?_⟩
    rw [mul_assoc, hx', inv_mul_cancel_left]
