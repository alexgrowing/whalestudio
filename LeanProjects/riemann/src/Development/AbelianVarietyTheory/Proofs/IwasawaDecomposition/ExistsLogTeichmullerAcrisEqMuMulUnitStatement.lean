import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLogTeichmullerAcrisEqMuMulUnit
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsCrisP
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_log_teichmuller_acris_eq_mu_mul_unit : ∀ (l : ℕ) [Fact l.Prime], ∀ e : Per.Fl l, e.untilt = 1 → ∃ (t u : Per.Acris l), IsLogA e t ∧ IsUnit u ∧ t = algebraMap (Per.Ainf l) (Per.Acris l) (mu e) * u := by
  first | exact @GlobalTheory.MemLoc.exists_isLogA | exact GlobalTheory.MemLoc.exists_isLogA | (intros; apply GlobalTheory.MemLoc.exists_isLogA <;> assumption)
