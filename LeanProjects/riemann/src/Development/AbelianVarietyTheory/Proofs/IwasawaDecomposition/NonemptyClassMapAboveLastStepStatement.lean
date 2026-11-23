import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NonemptyClassMapAboveLastStep
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StdLvPr
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.nonempty_classMap_above_lastStep : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → ∀ (u : B.Word) (a : I.ι) (i : ℕ), B.R.m < i → Nonempty ((I.stp u a i).Cl → (I.stp u I.mu0 i).Cl) := by
  first | exact @GlobalTheory.Mem.Col2.TC.nonempty_clDown | exact GlobalTheory.Mem.Col2.TC.nonempty_clDown | (intros; apply GlobalTheory.Mem.Col2.TC.nonempty_clDown <;> assumption)
