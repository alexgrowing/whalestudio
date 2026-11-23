import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsDiamondElementsStepLevels
import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemSmulLk
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.HAt Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_diamond_elements_step_levels : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (H : Formalism.L2.Herm.HermColsCh (I.rec7 l Z)) (F : ∀ u, FormsTiedSym (I.rec7 l Z) u (H.Ch u) (H.chOf u)), (∀ u, I.StdF l Z u (F u) ∧ I.StdLvC l Z u (F u)) → CarH H F → ∀ u i (hi : i ≤ (I.rec7 l Z).R.m) v (a : (((I.rec7 l Z).mem u).A.Fv v)ˣ), ∃ k : ℤ, (k : ((I.rec7 l Z).mem u).A.Fv v) = a ∧ (∀ h : i = 0 ∨ i = (I.rec7 l Z).R.m, ∃ δ, IsDia ((F u).cls i hi h).lev ((F u).atT.eV v).1 ((F u).atT.eV v).2 k δ) ∧ ∀ (h1 : 1 ≤ i) (h2 : i + 1 ≤ (I.rec7 l Z).R.m) (β : H.Ch u i), ∃ δ, IsDia ((F u).ch i h1 h2 β).lev ((F u).atT.eV v).1 ((F u).atT.eV v).2 k δ := by
  first | exact @GlobalTheory.Mem.Col2.HAt.exists_isDia_steps | exact GlobalTheory.Mem.Col2.HAt.exists_isDia_steps | (intros; apply GlobalTheory.Mem.Col2.HAt.exists_isDia_steps <;> assumption)
