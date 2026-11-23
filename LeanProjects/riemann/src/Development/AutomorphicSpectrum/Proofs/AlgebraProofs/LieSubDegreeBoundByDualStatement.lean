import Mathlib
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.LieSubDegreeBoundByDual
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.IsSplitGaussChars
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.GapCondExample
open GlobalTheory.CompanionTheory.Ar.Crv
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lie_sub_degree_bound_by_dual : ∀ (K : Type) [Field K] (C : ACurve K) (p : ℕ) [Fact p.Prime] [CharP K p] (O : Type) [CommRing O] [StarRing O] (d : ℕ) (D : ConjData C p O d), 2 < p → 0 ≤ deg C (dotDual C D.lie) ∧ ∀ W : Submodule K (Fin d → K), ((p : ℤ) - 2) * subDeg C D.lie W ≤ deg C (dotDual C D.lie) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Crv.FrobEst.frob_estimate | exact GlobalTheory.CompanionTheory.Ar.Crv.FrobEst.frob_estimate | (intros; apply GlobalTheory.CompanionTheory.Ar.Crv.FrobEst.frob_estimate <;> assumption)
