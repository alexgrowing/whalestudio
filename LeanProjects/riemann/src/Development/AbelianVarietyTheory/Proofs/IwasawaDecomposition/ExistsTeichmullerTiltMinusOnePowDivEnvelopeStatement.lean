import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsTeichmullerTiltMinusOnePowDivEnvelope
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsCrisP
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_teichmullerTiltMinusOne_pow_div_envelope : ∀ (l : ℕ) [Fact l.Prime], ∀ e : Per.Fl l, e.untilt = 1 → ∃ w : Per.Acris0 l, (l : Per.AinfP l) * (w : Per.AinfP l) = algebraMap (Per.Ainf l) (Per.AinfP l) (mu e) ^ (l - 1) ∧ (l : Per.Acris0 l) ∣ w ^ l := by
  first | exact @GlobalTheory.MemLoc.exists_mu_pow_div | exact GlobalTheory.MemLoc.exists_mu_pow_div | (intros; apply GlobalTheory.MemLoc.exists_mu_pow_div <;> assumption)
