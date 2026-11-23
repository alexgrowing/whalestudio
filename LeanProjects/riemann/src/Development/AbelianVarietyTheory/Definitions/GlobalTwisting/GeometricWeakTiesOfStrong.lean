import Mathlib
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.GoodReductionCondition
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MultW
import Formalism.SharpRestriction.DesignExistsOfChoices

noncomputable section

namespace GlobalTheory.Fc.S0

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.L2.Pj Formalism.IndefR.FWT
open scoped TensorProduct InnerProductSpace Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.PrimIn
open GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.Col2
open GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw

def RowRat : Prop :=
  StepW Start fun K B f T w => ∀ (Z : w.Lt) (hX : B.fields.Ok) (Wt : Set B.places.Pl) (z : GlobalTheory.Mem.R3.Dat (w.st Z) w.I hX T Wt), GrpTrue Z.N f → GlobalTheory.Mem.R3.GrpAt (w.st Z) w.I → DV.KapDef (w.D Z) → z.R.toRealDat.ExAt → GlobalTheory.RealGeo.InGeo z.geo → CoreP z → GIs2 K w Z.G → Wt = z.W1 (F0K K.s (w.D Z)) → (∀ v ∈ Wt, B.places.resChar v ∈ T.pl) → Formalism.IndefR.Rat.RowTest (z.R.toCx3 z.F)

end

open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Fc

variable (Q : V4.Slot) (Lk : LkT Bundle)

def CovolumeBound' : Prop := Row Q Lk (Ind.EvWC (Bd := Bundle) (fun _ => True) fun C CH _ _ _ b =>
  ((b.B.Q.Rl.toCx3 b.B.Q.F).data b.B.Q.F.cr false).L3 (b.B.Q.Rl.num b.B.Q.F C CH))

def FunctorialityCondition : Prop := Row Q Lk (Ind.EvWC (Bd := Bundle) (fun Fm => DIVinN Fm) fun C CH _ _ _ b =>
  ((b.B.Q.Rl.toCx3 b.B.Q.F).data b.B.Q.F.cr false).FUN (b.B.Q.Rl.num b.B.Q.F C CH))

def GeometricWeakCompatibility : Prop := Row Q Lk (AtAll fun D O c (b : Bundle D O c) => ∃ t : b.Comparison₂, Ind.PIota D O c (b.part t) ∧
  GlobalTheory.ExportPin.ClassSumPin (b.part t).pt ∧ (b.part t).pt.Ties ∧ GlobalTheory.BigOn.More (b.part t).pt)

def NL (𝒞 : FamClass) : Prop := Closed 𝒞 fun Fm _ => Formalism.MainNotions.LinkN Fm

variable {hL : GlobalTheory.Published.LocalLanglandsGL}

structure Open0 (p : Prm hL) : Prop where
  hPA : RL.At p R1.PeriodAdmissibilityAtBundlePoints
  hLamP : RL.At p R1.LambdaPositivityAtBundlePoints
  hDivG : RL.At p R1.DivisorConditionAtBundlePoints
  hDcPtG : RL.At p R1.DecompositionConditionAtBundlePoints
  selJ : RL.At p R1.JSelectionAtBundlePoints
  tie : RL.At p RL.Row_tie
  lab : RL.At p RL.LabelCondition
  good : RL.At p RL.GoodReductionCondition
  geo : RL.At p GeometricWeakCompatibility
  mi : RL.At p RL.MultiplicityCondition'
  kap : RL.At p RL.KappaCondition
  df : RL.At p RL.DifferentialCondition

theorem geometricWeakTies_of_strong {CF : ℝ} (h : RL.GeometricBoundCondition Q Lk CF) : GeometricWeakCompatibility Q Lk :=
  Row.imp h fun _ _ _ t _ Fm hc x hx i => let ⟨a, b, c, d, _, e, _⟩ := t Fm hc x hx i; ⟨a, b, c, d, e⟩

end GlobalTheory.Fc.S0

end
