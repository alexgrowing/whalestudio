import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OpenFirstParametersOfPublishedUE
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.BhattScholzeCrystallineLattices
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.BoundAtTwoThreeFamily
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.GeometricWeakTiesOfStrong
import Development.AbelianVarietyTheory.Definitions.Divisors.HypothesisBundleConversions
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Fc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.open_first_parameters_of_hypothesesUE : S0.HypothesesUE → ∀ (hL : GlobalTheory.Published.LocalLanglandsGL) (cDep : ℝ), S0.Open0 (prm1 hL cDep) := by
  first | exact @GlobalTheory.Fc.S0.Open0ProofU.open_of_hypothesesUE | exact GlobalTheory.Fc.S0.Open0ProofU.open_of_hypothesesUE | (intros; apply GlobalTheory.Fc.S0.Open0ProofU.open_of_hypothesesUE <;> assumption)
