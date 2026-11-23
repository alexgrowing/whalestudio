import Mathlib
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.TraceRowOperatorPowerDualWeylHighestWeight
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.GoodTopBot
import Development.AbelianVarietyTheory.PublishedTheorems.GlobalTheta.WeylDualWeylLatticesAgreeOfLowestAlcove
open MvPolynomial Formalism.GradedWeylDivisibility Formalism.BasicNotions GlobalTheory.Alc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.traceRowOperatorPower_dualWeyl_highestWeight : ∀ (N : ℕ) (ν : Fin N → ℕ), Antitone ν → ∀ k : ℕ, ∀ f ∈ dualWeyl ℚ N N ν, gel ℚ N N k f = hcVal ℚ (fun i => (ν i : ℚ)) k • f := by
  first | exact @GlobalTheory.Alc.gel_dualWeyl_rat | exact GlobalTheory.Alc.gel_dualWeyl_rat | (intros; apply GlobalTheory.Alc.gel_dualWeyl_rat <;> assumption)
