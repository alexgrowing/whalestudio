import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TrueColumnsPeriodMapDatumOkAndOverLevelPrime
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LatAtLattice
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.trueColumns_periodMapDatum_ok_and_over_levelPrime : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → ∀ u a, (I.perIn u a).Ok ∧ (I.perIn u a).Over (I.atIn u a) := by
  first | exact @GlobalTheory.Mem.Col2.PerLaw.perIn_laws | exact GlobalTheory.Mem.Col2.PerLaw.perIn_laws | (intros; apply GlobalTheory.Mem.Col2.PerLaw.perIn_laws <;> assumption)
