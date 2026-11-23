import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GL4HoweTheory.CondEx
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GL4HoweTheory.CharDual
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GL4HoweTheory.HoweConj
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GL4HoweTheory.HoweEx0
import Development.AutomorphicArithmetic.Foundations.Convolution.TwistedLocalOrbits.HoweSpace

open MeasureTheory ValuativeRel GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets UpperTheory.ConvolutionTheory.Loc

theorem UpperTheory.ConvolutionTheory.Loc.howeEx :
    ∀ (E : Type) [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E] (n : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin n) E) V), IsSmooth π → ∀ ϖ : Eˣ, valuation E (ϖ : E) = uniformizer E → GlobalTheory.LocGL.IsGeneric π → ∀ c : ℤ, ∃ a₀ : ℤ, ∀ a ≥ a₀,
      ∀ ψ : AddChar E Circle, HasConductor ψ (ϖ ^ (2 * a - c)) → howeSpace π ψ (howeSet n ϖ a c) ≠ ⊥ := by
  intro E _ _ _ _ n V _ _ π hs ϖ hϖ ⟨ψ₀, h1, h2, h3⟩ c
  obtain ⟨d, hd⟩ := UpperTheory.V.Z.Tf.L4.condEx E ϖ hϖ ψ₀ h1 h2
  obtain ⟨a₀, h⟩ := UpperTheory.V.Z.Tf.L4.howeEx0 E n V π hs ϖ hϖ ψ₀ d hd h3
  refine ⟨a₀, fun a ha ψ hψ => ?_⟩
  obtain ⟨β, hβ, e⟩ := UpperTheory.V.Z.Tf.L4.charDual E ϖ hϖ ψ₀ ψ d _ hd hψ
  refine UpperTheory.V.Z.Tf.L4.howeConj E n V π ϖ β a c _ hβ ψ₀ ψ e ?_
  rw [show c - (d - (2 * a - c)) = 2 * a - d by ring]
  exact h a ha
