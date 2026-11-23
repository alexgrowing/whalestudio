import Mathlib
import Formalism.DoubleCosetMeasures.StatementV
noncomputable section

open MeasureTheory Matrix ComplexConjugate Finset

namespace PI.DatumBlockEigen

def blockCond {F : Type} [Field F] (O : Subring F) (ϖ : F) {a t : ℕ}
    (J' : Subgroup (GL (Fin a) F)) (A : GL (Fin (a + t)) F) : Prop :=
  let M : Matrix (Fin a ⊕ Fin t) (Fin a ⊕ Fin t) F :=
    Matrix.reindex finSumFinEquiv.symm finSumFinEquiv.symm (A : Matrix (Fin (a + t)) (Fin (a + t)) F)
  (∃ k ∈ J', (k : Matrix (Fin a) (Fin a) F) = M.toBlocks₁₁) ∧
  (∀ i j, M.toBlocks₁₂ i j ∈ O) ∧
  M.toBlocks₂₁ ∈ Formalism.DoubleCosetMeasures.IIset O ϖ ∧
  (∃ D ∈ Formalism.DoubleCosetMeasures.GLint O t, (D : Matrix (Fin t) (Fin t) F) = M.toBlocks₂₂)

end PI.DatumBlockEigen

namespace PI

open PI.DatumBlockEigen in

def DatumBlockEigen : Prop :=
  ∀ (F : Type) [Field F] (O : Subring F) (ϖ : F), ϖ ∈ O → ϖ ≠ 0 → Formalism.DoubleCosetMeasures.IsLocalAt O ϖ →
    ∀ (a t : ℕ) (J' : Subgroup (GL (Fin a) F)),
    Formalism.DoubleCosetMeasures.congSub O ϖ a ≤ J' → J' ≤ Formalism.DoubleCosetMeasures.GLint O a →
    ∀ (ρ : J' →* ℂˣ), (∀ k : J', (k : GL (Fin a) F) ∈ Formalism.DoubleCosetMeasures.congSub O ϖ a → ρ k = 1) →
    ∀ h : GL (Fin (a + t)) F, blockCond O ϖ J' h →
      let Mi : Matrix (Fin a ⊕ Fin t) (Fin a ⊕ Fin t) F :=
        Matrix.reindex finSumFinEquiv.symm finSumFinEquiv.symm
          ((h⁻¹ : GL (Fin (a + t)) F) : Matrix (Fin (a + t)) (Fin (a + t)) F)
      ∃ k' : J', ((k' : GL (Fin a) F) : Matrix (Fin a) (Fin a) F) = Mi.toBlocks₁₁ ∧
        ∀ x : Matrix (Fin a ⊕ Fin t) (Fin a) F,
          Formalism.DoubleCosetMeasures.phiU O ϖ J' ρ (Mi * x) = ((ρ k' : ℂˣ) : ℂ) * Formalism.DoubleCosetMeasures.phiU O ϖ J' ρ x

end PI
