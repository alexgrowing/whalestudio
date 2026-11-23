import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.OrbitalIntegrals.BrMain
import Development.AutomorphicArithmetic.Foundations.Convolution.GeneralizedMeasures.LocHeckeInert

open NumberField IsDedekindDomain GroundTheory.Automorphic GroundTheory.Global GroundTheory.Global.SemiLocal PositivityTheory.Rg.Tf.Geo UpperTheory.ConvolutionTheory.GM

namespace UpperTheory.V.Z.Tf.Orb

def UnitSplit : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsGalois F E] (σ : E ≃ₐ[F] E),
    (∀ τ, τ ∈ Subgroup.zpowers σ) → (Module.finrank F E).Prime → ∀ n : ℕ, 0 < n → ∀ v : HeightOneSpectrum (𝓞 F), Split E v →
    MatchAt σ v 1 ((unitSet E n v).indicator 1) ((GLnLocal.integralGL (v.adicCompletion F) n : Set _).indicator 1)

theorem locUnit_of (hU : PositivityTheory.Rg.Tf.Loc.BCFLUnit) (hS : UnitSplit) : LocUnit := by
  intro F E _ _ _ _ _ _ σ hσ hp n hn v hu
  by_cases h : Split E v
  · exact hS F E σ hσ hp n hn v h
  · obtain ⟨w, hw⟩ := placeUniq_holds F E hp v h
    exact placeUnit_holds hU F E σ hσ v w hw (hu w) n

end UpperTheory.V.Z.Tf.Orb
