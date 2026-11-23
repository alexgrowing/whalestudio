import Formalism.LocalToGlobal.KernelLattices.ColumnData.ColumnDataEquations.SqFinal
import Formalism.LocalToGlobal.KernelLattices.ColumnData.ColumnDataEquations.MemSmulLat
import Formalism.LocalToGlobal.KernelLattices.ColumnData.BaseLinkOfNonzeroDelta

noncomputable section
open NumberField Formalism.BasicNotions Classical Matrix

namespace Formalism.L2.Ker.Cd.PairingIndexBounds.Eq.SquareSplitPairs

open Formalism.L2.PairingIndexBounds.Eq Formalism.L2.PairingIndexBounds

open Formalism.MainNotions Formalism.L2.Ker.Cd.PairingIndexBounds.Eq Formalism.L2.PairingIndexBounds.Eq

def SplitPair (D : Car) : Prop :=
  ∀ (N' : ℕ) (L' L'' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)), Even N' → SD D L' → SD D L'' →
    ∀ n : 𝓞 D.host.E, n ≠ 0 → ∃ e : Matrix (Fin N') (Fin N') D.host.E,
      (∀ y ∈ L', e *ᵥ y ∈ L') ∧ (∀ y ∈ L'', e *ᵥ y ∈ L'') ∧
      ∀ M ∈ ({e * e - e, (letI := D.host.cmStar; eᴴ) * e,
          (letI := D.host.cmStar; (1 - e)ᴴ) * (1 - e)} : Set (Matrix (Fin N') (Fin N') D.host.E)),
        ∀ y, (y ∈ L' ∨ y ∈ L'') → ∃ m, m ∈ L' ∧ m ∈ L'' ∧ M *ᵥ y = (n : D.host.E) • m

end Formalism.L2.Ker.Cd.PairingIndexBounds.Eq.SquareSplitPairs
