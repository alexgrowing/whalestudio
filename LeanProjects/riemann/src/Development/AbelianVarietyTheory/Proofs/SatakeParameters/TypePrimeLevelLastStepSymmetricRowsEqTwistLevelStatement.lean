import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.TypePrimeLevelLastStepSymmetricRowsEqTwistLevel
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.XiAtPenultimateEqXiCpl1
import Formalism.LocalToGlobal.Columns.KOneCharacterTrivialNearOne
import Formalism.LocalToGlobal.KernelLattices.TopPin
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.Mem.Col2
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.typePrimeLevel_lastStep_symmetricRows_eq_twistLevel : ∀ (X : Fields) (Pr : Primes X) (R : Ranks) (Ch : Chars X Pr R.m), X.Ok → Pr.Ok → Ch.Ok → levGTop Ch (rPsymF Ch) = twLt Ch R.m := by
  first | exact @GlobalTheory.levGTop_rPsymF_eq_twLt | exact GlobalTheory.levGTop_rPsymF_eq_twLt | (intros; apply GlobalTheory.levGTop_rPsymF_eq_twLt <;> assumption)
