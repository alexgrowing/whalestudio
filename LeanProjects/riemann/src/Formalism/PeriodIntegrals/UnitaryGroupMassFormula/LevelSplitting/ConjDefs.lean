import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LevelSplitting.SemidirectExistsOfParts

noncomputable section

namespace PI.LevelKSplit.W.CD

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain MeasureTheory PI.LevelKSplit
open scoped TensorProduct

section Ext

variable (F E : Type) [Field F] [NumberField F] [Field E] [Algebra F E]
  (σ : E →ₐ[F] E) (M : ℕ) (J : Matrix (Fin M) (Fin M) E)

def ModV : Prop :=
  IsHermND σ J → (∀ x, σ (σ x) = x) → ∀ g : HA (Af F) σ J,
    ∀ μ : Measure (Fin M → Af F ⊗[F] E), μ.IsAddHaarMeasure →
      μ.map (lin (Af F) σ J g) = μ

end Ext

def ModVAll : Prop := ForAllCM fun F E _ _ _ _ σ M J => ModV F E σ M J

end PI.LevelKSplit.W.CD
