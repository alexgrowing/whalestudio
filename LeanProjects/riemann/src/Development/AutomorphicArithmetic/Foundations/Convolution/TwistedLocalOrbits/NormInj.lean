import Development.AutomorphicArithmetic.Foundations.Convolution.TwistedLocalOrbits.Match
import Development.AutomorphicArithmetic.Foundations.Convolution.HermitianDescent.SeparableOfMap
import Development.AutomorphicArithmetic.Foundations.Convolution.HermitianDescent.GalField

open MeasureTheory ValuativeRel GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets PositivityTheory.Rg.Tf.Loc UpperTheory.ConvolutionTheory.Loc

private theorem inj {k E : Type} [Field k] [Field E] [Algebra k E] [FiniteDimensional k E] [IsGalois k E] (σ : E ≃ₐ[k] E)
    (hσ : ∀ τ : E ≃ₐ[k] E, τ ∈ Subgroup.zpowers σ) {n : ℕ} (δ δ' : GL (Fin n) E) (h : IsTwRegSemisimple σ δ)
    (e : (normGL σ δ' : Matrix (Fin n) (Fin n) E).charpoly = (normGL σ δ : Matrix (Fin n) (Fin n) E).charpoly) :
    TwConjugate (sigmaGL σ) δ δ' := by
  have hn : ∀ x : GL (Fin n) E, UpperTheory.ConvolutionTheory.D.nm σ (Module.finrank k E) x = normGL σ x := fun x => by
    unfold UpperTheory.ConvolutionTheory.D.nm normGL twNorm
    congr 2
    funext i
    rw [← sigmaGL_pow]
    rfl
  obtain ⟨x, hx⟩ := UpperTheory.ConvolutionTheory.D.nmInj k E σ _ (UpperTheory.ConvolutionTheory.D.galField k E σ hσ) n δ δ' (by rw [hn]; exact h) (by rw [hn, hn]; exact e)
  exact ⟨x, hx⟩

theorem UpperTheory.ConvolutionTheory.Loc.normInj :
    ∀ (k E : Type) [Field k] [CharZero k] [Field E] [Algebra k E] [FiniteDimensional k E] [IsGalois k E] (σ : E ≃ₐ[k] E),
      (∀ τ : E ≃ₐ[k] E, τ ∈ Subgroup.zpowers σ) → ∀ (n : ℕ) (γ : GL (Fin n) k), IsRegSemisimple γ → ∀ δ δ' : GL (Fin n) E,
        IsNormOf σ δ γ → IsNormOf σ δ' γ → TwConjugate (sigmaGL σ) δ δ' := by
  intro k E _ _ _ _ _ _ σ hσ n γ hγ δ δ' h h'
  have key : ∀ x : GL (Fin n) E, IsNormOf σ x γ → (normGL σ x : Matrix (Fin n) (Fin n) E).charpoly =
      (γ : Matrix (Fin n) (Fin n) k).charpoly.map (algebraMap k E) := fun x ⟨g, hg⟩ => by
    rw [hg, Units.val_mul, Units.val_mul, Matrix.coe_units_inv, Matrix.charpoly_units_conj, ← Matrix.charpoly_map]
    rfl
  refine inj σ hσ δ δ' ?_ ((key _ h').trans (key _ h).symm)
  unfold IsTwRegSemisimple
  rw [key _ h]
  exact Polynomial.Separable.map hγ
