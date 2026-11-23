import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FamilySplitOperatorsEqLabelOperatorsModels
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NormalFam
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
import Formalism.SatakeDualWeyl.KpqSubgroupCompact
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.Hk3
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.familySplitOperators_eq_labelOperators_models : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), R.toLevCh.Is A.μ0 → R.IsFam → R.IsModels → (∀ t h, IsOpsX R t h → ∀ (P : A.ok t) k, k ≤ D.sp.X'.rank → ∀ f, R.jX t (A.heckeR t (P, k) f) = h (R.pl P) (Finsupp.single (splitLab D.sp.X'.rank k) 1) (R.jX t f)) ∧ ∀ j t h, IsOpsV R j t h → ∀ (P : A.ok t) k, k ≤ (Vc D j).rank → ∀ f, R.jV j t (A.heckeL j t (P, k) f) = h (R.pl P) (Finsupp.single (splitLab (Vc D j).rank k) 1) (R.jV j t f) := by
  first | exact @GlobalTheory.SplitHeckeLabel.split_ops | exact GlobalTheory.SplitHeckeLabel.split_ops | (intros; apply GlobalTheory.SplitHeckeLabel.split_ops <;> assumption)
