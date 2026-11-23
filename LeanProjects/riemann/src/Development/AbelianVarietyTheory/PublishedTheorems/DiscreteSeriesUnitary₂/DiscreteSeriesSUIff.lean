import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ExistsIsHaarMeasureSUJ

namespace GlobalTheory.Published

open GlobalTheory.DSSU

def DiscreteSeriesSU : Prop :=
  ∀ n : ℕ, 2 ≤ n → ∀ ε : Fin n → Bool, ∃ F : Fam n, ParamS ε F ∧ ExhaustS ε F

theorem discreteSeriesSU_iff : DiscreteSeriesSU ↔ ∀ n : ℕ, 2 ≤ n → ∀ ε : Fin n → Bool, ClassS ε := Iff.rfl

end GlobalTheory.Published
