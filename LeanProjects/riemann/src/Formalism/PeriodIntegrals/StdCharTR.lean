import Mathlib
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes

noncomputable section

open MeasureTheory NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

namespace PI.StdCharTR

def Target : Prop :=
  ∀ (F : Type) [Field F] [NumberField F], NumberField.IsTotallyReal F → ∃ ψ : AddChar (AF F) ℂ, IsCharAF F ψ ∧
    ∀ x : Ainf F, psiInf F ψ x =
      Complex.exp (2 * Real.pi * Complex.I *
        ((∑ w : InfinitePlace F, (InfinitePlace.Completion.extensionEmbedding w (x w)).re : ℝ) : ℂ))

end PI.StdCharTR
