import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasDerivAtExpTwoAddSmulSinhcAdjoint
import Mathlib
import Formalism.SharpRestriction.Divisibility.SchurIrreducible
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ContinuousExptPY
open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.PolarU Matrix MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hasDerivAt_exp_two_add_smul_sinhcAdjoint : ∀ (p q : ℕ) (Y V : Mat p q) (a b : Ix p q), HasDerivAt (fun t : ℝ => NormedSpace.exp (Y + Y + t • V) a b) ((NormedSpace.exp Y * sAd Y V * NormedSpace.exp Y) a b) 0 := by
  first | exact @GlobalTheory.PolarU.hasDerivAt_exp_two_add_smul | exact GlobalTheory.PolarU.hasDerivAt_exp_two_add_smul | (intros; apply GlobalTheory.PolarU.hasDerivAt_exp_two_add_smul <;> assumption)
