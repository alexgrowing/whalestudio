import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StrictHenselianAcyclic
import Development.AbelianVarietyTheory.Definitions.Divisors.TwistedPlaceChoiceLiesOverPair

noncomputable section

namespace GlobalTheory.HeightCounting.Up

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting
  GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting

attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 2000000

def ListPin (D : D7) {I : Type} (Lc : Formalism.IndefR.Links.LevCh D I) (CF b : ℝ) : Prop :=
  ∃ G : GlobalTheory.ChiGrid.GridData Lc ⟨1, CF, b⟩,
    GlobalTheory.BigTop.Fun.FieldHas G (embLL0 D) ∧ GlobalTheory.LamTie.IsLamTieFull D.ntw (GlobalTheory.BigTop.Fun.lamOf G)

def ListSt (cDep : ℝ) {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} {P : Pre2 K w} (x : St P) : Prop :=
  ListPin (Dof x) x.m.z.R.toRealDat.toLevCh cDep K.s.b

variable (hL : GlobalTheory.Published.LocalLanglandsGL) (cDep : ℝ)

def NEl : NExt hL := fun K B f T w Z Wt p0 t nch n xd c => NEb hL K B f T w Z Wt p0 t nch n xd c ×
  PLift (ListPin (w.st Z).toD7 t.r.z.R.toRealDat.toLevCh cDep K.s.b)

def NElg : NExt hL := fun K B f T w Z Wt p0 t nch n xd c => NEl hL cDep K B f T w Z Wt p0 t nch n xd c × PLift (GoodO (w.D Z) nch xd)

def SettingsFormsExistList : Prop := AllSt fun _ _ _ _ _ P x => LI hL x → ∃ x' : St P, Nonempty (SettingsLevel hL x') ∧ ListSt cDep x'

def SeriesExistList : Prop := AllSt fun _ _ _ _ _ P x => SettingsLevel hL x → ∃ x' : St P, Nonempty (SeriesLevel hL x') ∧ (ListSt cDep x → ListSt cDep x')

def ModuliPointsExistList : Prop := AllSt fun _ _ _ _ _ P x => SeriesLevel hL x → ∃ x' : St P, Nonempty (StrictHenselianAcyclic hL x') ∧ (ListSt cDep x → ListSt cDep x')

def SFinl : Prop := AllSt fun K _ _ _ w P x => ∀ (l : LC hL x) (S : SExt) (Γ : GeoP), ListSt cDep x →
  ∃ (Z : w.Lt) (v : Lv3 (prmR (NEl hL cDep) S Γ).s K w Z), v.Wt = P.Wt ∧ Kept l.c.ch v.nch

def SecondNl : Prop := ∀ (S : SExt) (Γ : GeoP), Pass KPx (IsBuiltE (prmR (NEl hL cDep) S Γ).s) fun K B f T =>
  ∃ w : ColW B f T, Start K B f T w ∧ Has3 (prmR (NElg hL cDep) S Γ).s K B f T w

end GlobalTheory.HeightCounting.Up

end
