import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KernelsLattice
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsInvertibleIdealIndex
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Targets

open GroundTheory.Heights₂.Heights

def InvertibleIndexMul.Statement : Prop :=
  ∀ (Ω : Type) [Field Ω] (B : Subring Ω) (M N P : AddSubgroup Ω) (η : Type) [Fintype η] (g h : η → Ω),
    Module.Finite ℤ B →
    (∀ b ∈ B, ∀ z ∈ M, b * z ∈ M) → (∀ b ∈ B, ∀ z ∈ N, b * z ∈ N) → (∀ b ∈ B, ∀ z ∈ P, b * z ∈ P) →
    (∀ i, g i ≠ 0) → (∀ i, h i ≠ 0) →
    (∀ i, ∃ c ∈ B, c ≠ 0 ∧ c * g i ∈ B) → (∀ i, ∃ c ∈ B, c ≠ 0 ∧ c * h i ∈ B) →
    (∀ m : Ideal B, m.IsMaximal → ∃ i,
      ((∃ b : B, b ∉ m ∧ (b : Ω) * g i ∈ M) ∧ ∀ z ∈ M, ∃ b c : B, b ∉ m ∧ (b : Ω) * z = c * g i) ∧
      ((∃ b : B, b ∉ m ∧ (b : Ω) * h i ∈ N) ∧ ∀ z ∈ N, ∃ b c : B, b ∉ m ∧ (b : Ω) * z = c * h i) ∧
      ((∃ b : B, b ∉ m ∧ (b : Ω) * (g i * h i) ∈ P) ∧
        ∀ z ∈ P, ∃ b c : B, b ∉ m ∧ (b : Ω) * z = c * (g i * h i))) →
      0 < genIndex M B.toAddSubgroup ∧ 0 < genIndex N B.toAddSubgroup ∧
        genIndex P B.toAddSubgroup = genIndex M B.toAddSubgroup * genIndex N B.toAddSubgroup

end GroundTheory.Heights₂.Heights.Targets
