import Mathlib
import Formalism.LocalRingCardinality.PrincipalHermitianLattice

noncomputable section

namespace PI.GZeroLogBound

open Formalism.BasicNotions

def Conclusion0 (D : D7) : Prop :=
  ∀ Y : ℝ, (∀ i, (D.host.g i : ℝ) ≤ 2 * Y) → lam0 D ≤ 2 * (D.R.f : ℝ) * (D.R.r : ℝ) ^ 2 * Real.log (2 * Y)

def Target : Prop := ∀ D : D7, Conclusion0 D

end PI.GZeroLogBound
