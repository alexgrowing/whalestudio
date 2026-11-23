import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LevelFunctionalEqOfClassesRelatedAtPlace
import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemSmulLk
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.HAt Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.levelFunctional_eq_of_classes_related_at_place : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (H : Formalism.L2.Herm.HermColsCh (I.rec7 l Z)) (F : ∀ u, FormsTiedSym (I.rec7 l Z) u (H.Ch u) (H.chOf u)), (∀ u, I.StdF l Z u (F u) ∧ I.StdLvC l Z u (F u)) → CarH H F → ∀ u i (hi : i ≤ (I.rec7 l Z).R.m) v v' (c c' : ((I.rec7 l Z).mem u).C.cls i) (γ : GL (Fin ((I.rec7 l Z).R.N i)) (I.rec7 l Z).host.E), AdC (F u) i hi c c' γ ((F u).atT.eV v).1 → v' ≠ v → ∀ (z : Formalism.L2.Forms.Ld (I.rec7 l Z) u i hi c) (z' : Formalism.L2.Forms.Ld (I.rec7 l Z) u i hi c'), z.1 = γ.1 *ᵥ z'.1 → ((I.rec7 l Z).fm u).fv i v' c' (((F u).lv i hi).pr v' c' z') = ((I.rec7 l Z).fm u).fv i v' c (((F u).lv i hi).pr v' c z) := by
  first | exact @GlobalTheory.Mem.Col2.HAt.FvOff.fv_eq_of_adC | exact GlobalTheory.Mem.Col2.HAt.FvOff.fv_eq_of_adC | (intros; apply GlobalTheory.Mem.Col2.HAt.FvOff.fv_eq_of_adC <;> assumption)
