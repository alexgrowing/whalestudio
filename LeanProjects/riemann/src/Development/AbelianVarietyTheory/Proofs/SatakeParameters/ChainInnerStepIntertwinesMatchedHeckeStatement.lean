import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ChainInnerStepIntertwinesMatchedHecke
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
theorem _root_.GlobalTheory.T.chainInnerStep_intertwines_matchedHecke : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Chain.LiftInteg D → Core R F → SchurAll R → ∀ t P k, Good R t P → k + 1 < D.R.m → VacFix R.ψ (R.ωY t k) P → ∀ cS cT, Match R.ψ (R.ωY t k) P cS (dualC cT) → ∀ U U' : R.CC t (k + 1), (∀ v, U'.1 v = hk _ P cT (U.1 v)) → ∀ v, (R.ioY t k U').1 v = hk _ P cS ((R.ioY t k U).1 v) := by
  first | exact @GlobalTheory.ChainStepHecke.step_hk | exact GlobalTheory.ChainStepHecke.step_hk | (intros; apply GlobalTheory.ChainStepHecke.step_hk <;> assumption)
