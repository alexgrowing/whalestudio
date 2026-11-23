import Mathlib
import Formalism.DoubleCosetMeasures.StatementV
noncomputable section

open MeasureTheory Matrix ComplexConjugate Finset

namespace PI

def DatumConjInv : Prop :=
  ∀ (F : Type) [Field F] (O : Subring F) (ϖ : F) (a t : ℕ) (k : GL (Fin a) F),
    k ∈ Formalism.DoubleCosetMeasures.GLint O a → ∀ x : Matrix (Fin a ⊕ Fin t) (Fin a) F,
      Formalism.DoubleCosetMeasures.phiU O ϖ (Formalism.DoubleCosetMeasures.congSub O ϖ a) 1
                (Matrix.fromBlocks ((k⁻¹ : GL (Fin a) F) : Matrix (Fin a) (Fin a) F) 0 0
                  (1 : Matrix (Fin t) (Fin t) F) * x * (k : Matrix (Fin a) (Fin a) F)) =
        Formalism.DoubleCosetMeasures.phiU O ϖ (Formalism.DoubleCosetMeasures.congSub O ϖ a) 1 x

end PI
