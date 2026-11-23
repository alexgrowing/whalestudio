import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StepZeroClassesBijectiveSameDeco
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LatAtLattice
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cl0_bijective_and_deco_eq : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → ∀ u a b, Function.Bijective (I.cl0 u a b) ∧ ∀ c, ((I.stp u a 0).rep (I.cl0 u a b c)).1.1.deco = ((I.stp u I.mu0 0).rep c).1.1.deco := by
  first | exact @GlobalTheory.Mem.Col2.ClsZero.stepZero_classes_bijective_same_deco | exact GlobalTheory.Mem.Col2.ClsZero.stepZero_classes_bijective_same_deco | (intros; apply GlobalTheory.Mem.Col2.ClsZero.stepZero_classes_bijective_same_deco <;> assumption)
