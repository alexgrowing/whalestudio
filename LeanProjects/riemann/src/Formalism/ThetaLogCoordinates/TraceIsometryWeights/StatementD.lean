import Formalism.ThetaLogCoordinates.TraceIsometryWeights.HasLatBasis
import Formalism.ThetaLogCoordinates.TraceIsometryWeights.StatementC

namespace Formalism.InvariantFactorPaths.PW

open MvPolynomial Finset Formalism.GM.M

def DivInt : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (N r : ℕ) (LL : Letters N) (j : ℕ) (c d : Fin r), c ≠ d → ∀ (k : ℕ),
    ∀ x ∈ IntPol p (Fin N × Fin r), ((k.factorial : ℚ_[p]))⁻¹ • ((glAct p LL j c d) ^ k) x ∈ IntPol p (Fin N × Fin r)

def LatBasisPol : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (σ : Type) (U : Submodule ℚ_[p] (MvPolynomial σ ℚ_[p])), FiniteDimensional ℚ_[p] U →
    HasLatBasis p (IntPol p σ).toAddSubgroup U

end Formalism.InvariantFactorPaths.PW
