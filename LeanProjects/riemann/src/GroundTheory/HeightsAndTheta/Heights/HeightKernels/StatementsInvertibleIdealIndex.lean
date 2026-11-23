import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KernelsLattice
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open NumberField

noncomputable section

def InvertibleIdealIndex.Statement : Prop :=
  ∀ (L : Type) [Field L] [NumberField L] (B : Subring L) (M : AddSubgroup L) (ι : Type) [Fintype ι]
    (a : ι → L),
    Module.Finite ℤ B →
    (∀ b ∈ B, ∀ z ∈ M, b * z ∈ M) →
    (∀ i, a i ∈ M) →
    (∀ i, ∃ c ∈ B, c ≠ 0 ∧ c * a i ∈ B) →
    (∀ m : Ideal B, m.IsMaximal → ∃ i, ∀ z ∈ M, ∃ b c : B, b ∉ m ∧ (b : L) * z = c * a i) →
      (Module.finrank ℚ L : ℝ) * Real.log (genIndex M B.toAddSubgroup) =
        (Module.finrank ℤ B : ℝ) *
          Real.log (genIndex (Submodule.span (𝓞 L) (Set.range a)).toAddSubgroup
            (1 : Submodule (𝓞 L) L).toAddSubgroup)

end

end GroundTheory.Heights₂.Heights
