import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.SelmerRankBounds.EllipticityFromProductFormula
open MeasureTheory NumberField IsDedekindDomain Polynomial
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace GroundTheory.Global GroundTheory.Global.SemiLocal
open GroundTheory.Global.AdeleBaseChange
open PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Loc PositivityTheory.Rg.Tf.Geo
open scoped ENNReal NumberField.AdeleRing TensorProduct

theorem UpperTheory.charpoly_eq_of_norm_eq_of_twisted_conj :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsGalois F E] (σ : E ≃ₐ[F] E),
        (∀ τ : E ≃ₐ[F] E, τ ∈ Subgroup.zpowers σ) → ∀ n : ℕ, 0 < n → ∀ (δ δ' h : GL (Fin n) E) (γ γ' : GL (Fin n) F), normGL σ δ = incl γ → normGL σ δ' = incl γ' →
        δ' = h⁻¹ * δ * sigmaGL σ h → (γ : Matrix (Fin n) (Fin n) F).charpoly = (γ' : Matrix (Fin n) (Fin n) F).charpoly := by
  intro F E _ _ _ _ _ _ σ _ n _ δ δ' h γ γ' hγ hγ' hδ
  have hℓ : σ ^ Module.finrank F E = 1 := by
    rw [← IsGalois.card_aut_eq_finrank]; exact pow_card_eq_one'
  have hθ : (sigmaGL σ : Monoid.End (GL (Fin n) E)) ^ Module.finrank F E = 1 := by
    rw [← sigmaGL_pow, hℓ, sigmaGL_one]
  have h1 : normGL σ δ' = h⁻¹ * normGL σ δ * h := by
    rw [hδ]
    exact twNorm_twConj_of_pow_eq_one (sigmaGL σ) hθ h δ
  rw [hγ, hγ'] at h1
  have hv : ∀ g : GL (Fin n) F, ((incl g : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) =
      (g : Matrix (Fin n) (Fin n) F).map (algebraMap F E) := fun _ => rfl
  apply Polynomial.map_injective (algebraMap F E) (algebraMap F E).injective
  rw [← Matrix.charpoly_map, ← Matrix.charpoly_map, ← hv, ← hv, h1, Units.val_mul, Units.val_mul,
    Matrix.coe_units_inv, Matrix.charpoly_units_conj']
