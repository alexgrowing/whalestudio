import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsSplitPrimeHeckeTransferCompositeLift
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
theorem _root_.GlobalTheory.T.exists_splitPrime_heckeTransfer_compositeLift : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Chain.LiftInteg D → Core R F → SchurAll R → ∀ t (P : A.ok t), ∃ z : ℕ → ℕ → ℂ, (∀ k, k ≤ D.sp.X'.rank → MatchE R t (R.pl P) (Finsupp.single (splitLab D.sp.X'.rank k) 1) (splitC (Yc D 0).rank (z k))) ∧ ∀ a : ℕ → ℂ, Formalism.L2.Col.heckePolyOf D.sp.X'.rank (A.q P) (fun k => ∑ j ∈ Finset.range ((Yc D 0).rank + 1), z k j * a j) = (Formalism.L2.Col.heckePolyOf (Yc D 0).rank (A.q P) a).comp (C ((A.q P : ℂ) ^ (D.R.m / 2 * D.R.t)) * X) * ((A.fam.R t).blockProd P).map D.what₂.embLL := by
  first | exact @GlobalTheory.Hk3.SplitChain.exists_transfer | exact GlobalTheory.Hk3.SplitChain.exists_transfer | (intros; apply GlobalTheory.Hk3.SplitChain.exists_transfer <;> assumption)
