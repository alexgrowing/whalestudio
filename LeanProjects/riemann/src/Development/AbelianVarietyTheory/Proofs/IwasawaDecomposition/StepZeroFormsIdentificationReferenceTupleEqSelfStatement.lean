import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StepZeroFormsIdentificationReferenceTupleEqSelf
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StdLvPr
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.stepZeroFormsIdentification_referenceTuple_eq_self : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (l0 : I.Law0 l) (u : B.Word) (x : ((I.fm l u I.mu0).lat 0).V), (l0 u I.mu0).choose x = x := by
  first | exact @GlobalTheory.Mem.Col2.TC.MuZeroForms.law0_choose_mu0_eq_self | exact GlobalTheory.Mem.Col2.TC.MuZeroForms.law0_choose_mu0_eq_self | (intros; apply GlobalTheory.Mem.Col2.TC.MuZeroForms.law0_choose_mu0_eq_self <;> assumption)
