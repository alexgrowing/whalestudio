import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FockModelDualPairCasimirApply
import Formalism.SharpRestriction.Divisibility.SchurIrreducible
import Formalism.LocalToGlobal.BesselHermitianTheta.DefsReal
open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fockModel_dualPair_casimir_apply : ∀ (p q r s : ℕ) (P : Pol p q r s), casimir (fockAct2 p q r s) P = casimir (fockAct1 p q r s) P - ((((p + q : ℕ) : ℂ) * ((r + s : ℕ) : ℂ) * (((r + s : ℕ) : ℂ) - ((p + q : ℕ) : ℂ))) / 4) • P := by
  first | exact @GlobalTheory.fock_casimir_apply | exact GlobalTheory.fock_casimir_apply | (intros; apply GlobalTheory.fock_casimir_apply <;> assumption)
