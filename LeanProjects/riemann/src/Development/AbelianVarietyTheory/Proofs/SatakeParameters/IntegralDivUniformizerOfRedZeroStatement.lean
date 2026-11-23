import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IntegralDivUniformizerOfRedZero
import Mathlib
import Formalism.LocalToGlobal.Columns.FiniteSumNonzeroLargeDepth
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_div_uniformizer_of_red_zero : ∀ (X : Fields) (Pr : Primes X), X.Ok → Pr.Ok → ∀ w ∈ Pr.vGs, ∀ a : X.E, IntAt w a → redP w a = 0 → IntAt w (a / (qOf w : X.E)) := by
  first | exact @GlobalTheory.TypePrimeUnif.intAt_div_qOf | exact GlobalTheory.TypePrimeUnif.intAt_div_qOf | (intros; apply GlobalTheory.TypePrimeUnif.intAt_div_qOf <;> assumption)
