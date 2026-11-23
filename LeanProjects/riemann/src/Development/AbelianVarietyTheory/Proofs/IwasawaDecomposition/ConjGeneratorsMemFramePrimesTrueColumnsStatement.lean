import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ConjGeneratorsMemFramePrimesTrueColumns
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FieldTies
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NonzeroPlacesOverPrimes
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LargeFor
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Theta GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.AtMember
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.conjGenerators_mem_framePrimes_trueColumns : ∀ (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : Bl.ColW B f T) (Z : w.Lt) (t : Bl.ColT w Z), HalfAt (Formalism.L2.Herm.toErrXS t.full.1) (Fr.at (w.st Z) f) := by
  first | exact @GlobalTheory.AtMember.conj_gen_mem_frame | exact GlobalTheory.AtMember.conj_gen_mem_frame | (intros; apply GlobalTheory.AtMember.conj_gen_mem_frame <;> assumption)
