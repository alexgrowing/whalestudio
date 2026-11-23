import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CongruentAutomorphismsLiftStepGroupElements
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LiftsInvOne
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.AdT Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.congruent_automorphisms_lift_step_group_elements : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → ∀ (u : B.Word) (a : I.ι) (i : ℕ) (hi : i < B.R.m) (b : (I.stp u a i).β) (P : SBof I a) (g : Sp B.fields.E (B.R.N i) ≃ₗ[B.fields.E] Sp B.fields.E (B.R.N i)) (z : B.fields.K), MidAt I hi b P g z → g ∈ Formalism.L2.Col.GLint B.fields.E (B.R.N i) P.1 ∧ ∀ g' ∈ Formalism.L2.Col.GLint B.fields.E (B.R.N i) P.1, CongE P.1 ((I.cst a).D P) g g' → ∃ κ : (I.stp u a i).G b, (I.stp u a i).gam b κ = 1 ∧ LiftsInv I κ P g' ∧ ∀ P', P' ≠ P → LiftsInv I κ P' 1 := by
  first | exact @GlobalTheory.Mem.Col2.AdT.midAt_lifts | exact GlobalTheory.Mem.Col2.AdT.midAt_lifts | (intros; apply GlobalTheory.Mem.Col2.AdT.midAt_lifts <;> assumption)
