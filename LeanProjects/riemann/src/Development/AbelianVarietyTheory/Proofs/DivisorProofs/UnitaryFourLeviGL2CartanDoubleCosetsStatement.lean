import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryFourLeviGL2CartanDoubleCosets
import Mathlib
import Formalism.SatakeDualWeyl.KpqSubgroupCompact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AntiJMulApply
open Formalism.UG GlobalTheory.SatakeWeyl
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitaryFourLeviGL2_cartan_doubleCosets : GlobalTheory.SatakeWeyl.CartanFour := by
  first | exact @GlobalTheory.SatakeWeyl.Four.cartanFour | exact GlobalTheory.SatakeWeyl.Four.cartanFour | (intros; apply GlobalTheory.SatakeWeyl.Four.cartanFour <;> assumption)
