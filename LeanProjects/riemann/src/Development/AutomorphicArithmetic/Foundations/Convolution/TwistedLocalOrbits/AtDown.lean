import Development.AutomorphicArithmetic.Foundations.Convolution.GeneralizedMeasures.MatchOne
import Development.AutomorphicArithmetic.Foundations.Convolution.TwistedLocalOrbits.PlaceDown

open MeasureTheory NumberField IsDedekindDomain ValuativeRel GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets PositivityTheory.Rg.Tf.Loc UpperTheory.ConvolutionTheory.Loc GroundTheory.Global GroundTheory.Global.SemiLocal
open PositivityTheory.Rg.Tf.Geo (mapGL incFin galFin)

theorem UpperTheory.ConvolutionTheory.Loc.atDown :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsGalois F E] (σ : E ≃ₐ[F] E),
      (∀ τ : E ≃ₐ[F] E, τ ∈ Subgroup.zpowers σ) → ∀ (v : HeightOneSpectrum (𝓞 F)) (w : PlacesOver E v), (∀ w' : PlacesOver E v, w' = w) → ∀ n : ℕ,
      ∃ ρ : ValueGroupWithZero (w.1.adicCompletion E), 0 < ρ ∧ ∀ φ ∈ SB (GL (Fin n) (w.1.adicCompletion E)), Function.support φ ⊆ ball n ρ →
        ∃ f ∈ SB (GL (Fin n) (v.adicCompletion F)), UpperTheory.ConvolutionTheory.GM.MatchAt σ v 1 (fun g => φ (UpperTheory.ConvolutionTheory.GM.cmp w g)) f := by
  intro F E _ _ _ _ _ _ σ hσ v w hw n
  obtain ⟨i1, i2, i3, i4, mE, mF, hE, hF, h1, h2⟩ := (UpperTheory.ConvolutionTheory.GM.matchOne F E σ n v).1
  obtain ⟨ρ, hρ, h⟩ := UpperTheory.ConvolutionTheory.Loc.placeDown F E σ hσ v w hw n mE mF hE hF
  refine ⟨ρ, hρ, fun φ ha hs => ?_⟩
  obtain ⟨f, hb, hm⟩ := h φ ha hs
  exact ⟨f, hb, @(UpperTheory.ConvolutionTheory.GM.matchOne F E σ n v).2 i1 i2 i3 i4 mE mF hE hF h1 h2 _ _ _ hm⟩
