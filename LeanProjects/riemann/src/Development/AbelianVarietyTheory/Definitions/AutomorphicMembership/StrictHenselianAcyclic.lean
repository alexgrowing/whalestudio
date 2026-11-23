import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RootsOfUnityRingLeWittIntegers
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NonzeroPlacesOverPrimesLifts
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ThetaChr
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.BuiltEx
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TwistDataAgreeAcrossCoefficients

noncomputable section

namespace GlobalTheory.HeightCounting.Up

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting
  GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting

attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option synthInstance.maxHeartbeats 400000
set_option genInjectivity false
set_option genSizeOfSpec false
set_option maxHeartbeats 2000000

variable {hL : GlobalTheory.Published.LocalLanglandsGL} {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} {P : Pre2 K w}

abbrev Dof (x : St P) : D7 := (w.st x.o.Z).toD7

abbrev cfOf (x : St P) : CharFrame (Dof x) := TC.cf w.I w.l x.o.Z

open Classical in

def QOf (P : Pre2 K w) (v : B.places.Pl) : Finset (HeightOneSpectrum (𝓞 B.host.E)) := if v ∈ P.Wt then T.Q v else ∅

structure LA (hL : GlobalTheory.Published.LocalLanglandsGL) (x : St P) : Type 1 where
  a : StA hL (Dof x) (cfOf x) (repOf x.r.Y)
  Pq : HeightOneSpectrum (𝓞 (maximalRealSubfield (Dof x).host.E)) → PlE (Dof x).host
  Pq_over : ∀ v, NG.OverPl (Pq v) v
  sel : Set.range Pq = Set.range w.I.sel

structure LI (hL : GlobalTheory.Published.LocalLanglandsGL) (x : St P) : Type 1 extends LA hL x where
  mt : InMt x.r.Y (cfOf x) w.I.xi (QOf P)
  rat : InRat x.r.Y x.m.z.cG
  cusp : RowCusp (Dof x) a.A.row

structure SettingsLevel (hL : GlobalTheory.Published.LocalLanglandsGL) (x : St P) : Type 1 extends LI hL x where
  b : SettingsFormsState a rat Pq

structure SeriesLevel (hL : GlobalTheory.Published.LocalLanglandsGL) (x : St P) : Type 1 extends LI hL x where
  b : SeriesState x.m.z.geo a rat mt.ad.PV Pq

structure StrictHenselianAcyclic (hL : GlobalTheory.Published.LocalLanglandsGL) (x : St P) : Type 1 extends LI hL x where
  b : ModuliPointsState x.m.z.geo a rat mt.ad.PV Pq

structure LC (hL : GlobalTheory.Published.LocalLanglandsGL) (x : St P) : Type 1 extends StrictHenselianAcyclic hL x where
  c : StC mt b T.k T.psi

abbrev AllSt (p : ∀ (K : Ctx) (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T) (P : Pre2 K w), St P → Prop) : Prop :=
  StepW Start fun K B f T w => ∀ (P : Pre2 K w) (x : St P), p K B f T w P x

variable (hL)

def NEb : NExt hL := fun K B f T w Z Wt p0 t nch n xd c => NE hL K B f T w Z Wt p0 t nch n xd c × PLift (BkLaw (w.D Z))

def SA : Prop := AllSt fun _ _ _ _ _ P x => IsEmpty x.o.N.nd.Loc →
  ∃ x' : St P, Nonempty (LA hL x') ∧ GlobalTheory.TwistChoice.SameGalois (Dof x).nd (Dof x').nd

def SMt : Prop := AllSt fun _ _ _ _ w P x => Nonempty (InMt x.r.Y (cfOf x) w.I.xi (QOf P))

def SRat : Prop := AllSt fun _ _ _ _ _ _ x => LA hL x → Nonempty (InRat x.r.Y x.m.z.cG)

def SCusp : Prop := AllSt fun _ _ _ _ _ _ x => ∀ l : LA hL x, RowCusp (Dof x) l.a.A.row

def SettingsFormsExist : Prop := AllSt fun _ _ _ _ _ P x => LI hL x → ∃ x' : St P, Nonempty (SettingsLevel hL x')

def SeriesExist : Prop := AllSt fun _ _ _ _ _ P x => SettingsLevel hL x → ∃ x' : St P, Nonempty (SeriesLevel hL x')

def SB2 : Prop := AllSt fun _ _ _ _ _ P x => SeriesLevel hL x → ∃ x' : St P, Nonempty (StrictHenselianAcyclic hL x')

def SC : Prop := AllSt fun _ _ _ T _ _ x => ∀ l : StrictHenselianAcyclic hL x, Nonempty (StC l.mt l.b T.k T.psi)

def SEta : Prop := AllSt fun _ _ _ _ _ P x => ∀ l : LC hL x,
  GlobalTheory.CoefDuty.BuiltEx l.a.A l.mt.M l.c.ch l.c.tp.tup → GlobalTheory.CoefDuty.EvO l.a.A l.mt.M l.c.ch l.c.tp.tup fun D' =>
    GlobalTheory.CoefDuty.Large D' ∧ ∀ j v, 1 ≤ j → j ≤ (Dof x).R.m → ∀ v' : D'.what₂.places.Pl, HEq v' v → D'.what₂.etaJ j v' = P.q.eta j v

structure Kept {D D' : D7} (c : NChoice D) (c' : NChoice D') : Prop where
  gal : GlobalTheory.TwistChoice.SameGalois D.nd D'.nd
  set : GlobalTheory.TwistChoice.TwistDataAgreeAcrossCoefficients D.ntw D'.ntw
  forms : GlobalTheory.TwistChoice.SameForms D.nexp D'.nexp
  br : HEq D.ntwbr D'.ntwbr
  twI : HEq c.twI c'.twI
  sd : HEq c.sd c'.sd
  Q : HEq c.Q c'.Q
  k : HEq c.k' c'.k'
  psi : HEq c.psi' c'.psi'

def SFin : Prop := AllSt fun K _ _ _ w P x => ∀ (l : LC hL x) (S : SExt) (Γ : GeoP),
  ∃ (Z : w.Lt) (v : Lv3 (prmR (NEb hL) S Γ).s K w Z), v.Wt = P.Wt ∧ Kept l.c.ch v.nch

def NEg : NExt hL := fun K B f T w Z Wt p0 t nch n xd c => NEb hL K B f T w Z Wt p0 t nch n xd c × PLift (GoodO (w.D Z) nch xd)

def SecondN : Prop := ∀ (S : SExt) (Γ : GeoP), Pass KPx (IsBuiltE (prmR (NEb hL) S Γ).s) fun K B f T =>
  ∃ w : ColW B f T, Start K B f T w ∧ Has3 (prmR (NEg hL) S Γ).s K B f T w

end GlobalTheory.HeightCounting.Up

end
