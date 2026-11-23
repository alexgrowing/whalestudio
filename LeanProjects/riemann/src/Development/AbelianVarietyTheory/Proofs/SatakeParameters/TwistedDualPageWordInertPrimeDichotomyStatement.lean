import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.TwistedDualPageWordInertPrimeDichotomy
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Alternates
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
import Formalism.FrobeniusOrbits.HostCorollaries
open GlobalTheory.HTW Formalism.BasicNotions Formalism.FrobeniusOrbits
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twistedDualPageWord_inert_prime_dichotomy : ∀ {D : D7} (L : SizeData₂ D) (C : ℝ) (j : Fin D.R.m) (ε : ℤˣ) (τ φ : D.R.GG) (l : ℕ), Roomy L C → 11 ≤ l → φ.1.2 = -1 → (pageWord L j ε τ φ).Box ∧ ((pageWord L j ε τ φ).HypNT ∨ (φ = D.R.cc ∧ (pageWord L j ε τ φ).HypAT l ∧ ∀ i, (pageWord L j ε τ φ).thick i)) := by
  first | exact @GlobalTheory.HTW.pageWord_inert_dichotomy | exact GlobalTheory.HTW.pageWord_inert_dichotomy | (intros; apply GlobalTheory.HTW.pageWord_inert_dichotomy <;> assumption)
