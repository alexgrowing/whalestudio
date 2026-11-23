import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaJetIntegralityTypePrimeOfSplitTableBound
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.JetSplitAmb
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.JetOpIntegral
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.MemRatIdxOfJetsRatDeg
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.JetsInIffStepField
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.ValidForConstructedPointClassesEventuallyWorking
import Formalism.SharpRestriction.ElevenLe
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.AtG
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaJetIntegrality_typePrime_of_splitTableBound : JetSplitAmb → ∀ (D : D7) (EX : ErrX D) (sel : _) (δ : ℂ) (B : Base D D.host.ccK δ) (χ : _) (cD : _), GlobalTheory.ColPeriod.JetLossAll D EX sel B χ cD := by
  first | exact @GlobalTheory.JetsFromTables.jetLossAll_of_jetSplitAmb | exact GlobalTheory.JetsFromTables.jetLossAll_of_jetSplitAmb | (intros; apply GlobalTheory.JetsFromTables.jetLossAll_of_jetSplitAmb <;> assumption)
