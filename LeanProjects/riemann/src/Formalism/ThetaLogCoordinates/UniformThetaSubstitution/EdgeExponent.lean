import Mathlib
import Formalism.ThetaLogCoordinates.UniformThetaSubstitution.StatementC

noncomputable section

open scoped BigOperators
open Finset

namespace Formalism.InvariantFactorPaths.G7

def EdgeExponent : Prop :=
  ∀ (ι : Type) (Ev Od : Finset ι) (lam : ι → ℕ → ℤ) (wj X : ι → ℤ) (i : ℕ),
    NprimeZ Ev Od lam wj i + ∑ s ∈ Ev, ((i : ℤ) * wj s - X s) + ∑ s ∈ Od, (X s - (i : ℤ) * wj s) =
      ∑ s ∈ Od, X s + ∑ s ∈ Ev, (∑ a ∈ Icc 1 i, (lam s a + wj s) - X s)

def EdgeNonneg : Prop :=
  ∀ (μ : YoungDiagram) (B : Type) [DecidableEq B] (I : ℕ → Finset B) (J : Finset B),
    (∀ c, (I c).card = μ.colLen c) →
    ∑ c ∈ range (μ.rowLen 0), (I c ∩ J).card ≤ ∑ a ∈ range J.card, μ.rowLen a

end Formalism.InvariantFactorPaths.G7
