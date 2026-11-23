import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.AdelicFiniteDatumIntegralOffBadPrimes
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.UnderTie
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV GlobalTheory.TwU GlobalTheory.TwV
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adelicFiniteDatum_integralOffBadPrimes : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a => PtEx A a → ∀ i hi β β' x x' z, IntOff (t.O u μ).S (xiAd A a i hi β β' x x' z)) := by
  first | exact @GlobalTheory.TwV.xiAd_intOff | exact GlobalTheory.TwV.xiAd_intOff | (intros; apply GlobalTheory.TwV.xiAd_intOff <;> assumption)
