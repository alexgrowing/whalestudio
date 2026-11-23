import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.NGAnalytic
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LocClosed
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.AtBase

noncomputable section

open scoped Classical
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full
  Formalism.FourierDecayAlt Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc

namespace GlobalTheory.SnFam

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def ampQ {Cl Nu : Type} (Q : Prop → Prop) (L : PN.LocalNG Cl Nu) (d : ∀ p, L.D p) : ℂ :=
  haveI := L.fP
  ∑ A ∈ L.Om.powerset.filter (fun A => Q A.Nonempty), ∏ p, (if p ∈ A then L.aN p (d p) else L.aZ p (d p))

variable {D : D7} {X : HidaSetting D} (Y : Full X) (u u' : D.what₂.Word)

def setQ (Q : Prop → Prop) : Set (TauC Y u u') := {t | (Y.tO u u').G t ≠ 0 ∧ Q (¬ (Y.tO u u').gener t)}

def FamQ {Cl : Type} (Q : Prop → Prop) (TS : Set (TauC Y u u')) (cls : TauC Y u u' → Cl) : Prop :=
  TS = setQ Y u u' Q ∧ GlobalTheory.Unfold.ClsRow TS cls ∧
    ∀ t ∈ TS, ∀ t' ∈ TS, cls t = cls t' → (Y.tO u u').rowOf t = (Y.tO u u').rowOf t'

def HasPt (TS : Set (TauC Y u u')) (γ : PN.Pts D.host.E D.R.rS) : Prop :=
  ∃ t ∈ TS, (Y.tO u u').vec t ≠ 0 ∧ ptPN t = γ

def grpF {Cl : Type} (TS : Set (TauC Y u u')) (cls : TauC Y u u' → Cl) (c : Cl) (γ : PN.Pts D.host.E D.R.rS) (ν : NuC D) :=
  ∑' t : TauC Y u u', (TS ∩ {t | cls t = c ∧ ptPN t = γ ∧ nmlOf Y u u' t = ν}).indicator (Y.tO u u').vec t

def a2F {Cl : Type} (TS : Set (TauC Y u u')) (cls : TauC Y u u' → Cl) (νq : X.B.I.Ginf → Measure X.B.I.Ginf)
    (c : Cl) (γ : PN.Pts D.host.E D.R.rS) (ν : NuC D) : ℝ :=
  ‖grpF Y u u' TS cls c γ ν‖ ^ 2 / J2of Y u u' νq γ

def gCls (t : TauC Y u u') : Set (TauC Y u u') :=
  {t' | t' ∈ (Y.tO u u').genSet ∧ (Y.tO u u').rowOf t' = (Y.tO u u').rowOf t ∧ (Y.tO u u').s0 t t' = 1 ∧
    (Y.tO u u').scal t t'}

def locOf (t : TauC Y u u') (p : PlF D) : Loc.Term (Vp D p) (Y.M p) D.R.rS :=
  GlobalTheory.LocOver.locU (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p t.toTerm.lam (lf D (X.Fu u)) (Quot.out t.toTerm.cls).1 (Tu D u) (Tu D u')

def Dfc (t : TauC Y u u') : Set (PlF D) :=
  {p | LocNG.BBne (H := locH (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p) (locOf Y u u' t p)}

end GlobalTheory.SnFam
