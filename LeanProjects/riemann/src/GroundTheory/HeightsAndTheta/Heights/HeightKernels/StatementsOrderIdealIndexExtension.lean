import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsInvertibleIdealIndex
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open NumberField

noncomputable section

def OrderIdealIndexExtension.Statement : Prop :=
  ∀ (L : Type) [Field L] [NumberField L] (B : Subring L), Module.Finite ℤ B →
    ∃ (r : ℕ) (s : B), s ≠ 0 ∧ Module.finrank ℚ L = r * Module.finrank ℤ B ∧
      (∀ I : Ideal B, I ≠ ⊥ → I.toAddSubgroup.index ≠ 0) ∧
      ∀ I : Ideal B, I ≠ ⊥ → (I.IsPrincipal ∨ I ⊔ Ideal.span {s} = ⊤) →
        (Submodule.span (𝓞 L) ((fun y : B => (y : L)) '' (I : Set B))).toAddSubgroup.relIndex
            (1 : Submodule (𝓞 L) L).toAddSubgroup = I.toAddSubgroup.index ^ r

end

end GroundTheory.Heights₂.Heights
