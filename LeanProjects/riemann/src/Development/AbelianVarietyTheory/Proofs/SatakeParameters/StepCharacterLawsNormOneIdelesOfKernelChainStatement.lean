import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.StepCharacterLawsNormOneIdelesOfKernelChain
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.UnderTie
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV GlobalTheory.TwU GlobalTheory.TwV
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.stepCharacterLaws_normOneIdeles_of_kernelChain : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a => MuLaw t u μ dtU) := by
  first | exact @GlobalTheory.TwV.MuLawPf.muLaw_underTie | exact GlobalTheory.TwV.MuLawPf.muLaw_underTie | (intros; apply GlobalTheory.TwV.MuLawPf.muLaw_underTie <;> assumption)
