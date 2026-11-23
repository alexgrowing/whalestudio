import Mathlib
import Formalism.MeanHeightDescent.DescentCut
import Formalism.MeanHeightDescent.AverageDegreeBounds.CovolumeIntoDivisionHolds

open Module NumberField

noncomputable section

namespace Formalism.ExtensionFiltration

open Formalism.HN

theorem rkK_pos {K V ι : Type} [Field K] [NumberField K] [AddCommGroup V] [Module K V]
    [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [Fintype ι] (b : Basis ι K V)
    (A : Submodule (𝓞 K) V) (hA : A ≠ ⊥) : 0 < rkK (K := K) A := by
  haveI : FiniteDimensional K V := Module.Finite.of_basis b
  unfold rkK
  rw [Nat.pos_iff_ne_zero, Ne, Submodule.finrank_eq_zero]
  intro h
  apply hA
  rw [eq_bot_iff]
  intro x hx
  have hx' : x ∈ Submodule.span K (A : Set V) := Submodule.subset_span hx
  rw [h, Submodule.mem_bot] at hx'
  simp [hx']

end Formalism.ExtensionFiltration
