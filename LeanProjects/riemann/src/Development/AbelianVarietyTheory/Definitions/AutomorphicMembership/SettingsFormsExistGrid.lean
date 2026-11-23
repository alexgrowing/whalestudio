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

def GridPin (D : D7) {I : Type} (Lc : Formalism.IndefR.Links.LevCh D I) (CF b : ℝ) : Prop :=
  ∃ G : GlobalTheory.ChiGrid.GridData Lc ⟨1, CF, b⟩,
    GlobalTheory.BigTop.Fun.FieldHas G (embLL0 D) ∧ GlobalTheory.LamTie.IsLamTieFull D.ntw (GlobalTheory.BigTop.Fun.lamOf G)

def GridSt {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} {P : Pre2 K w} (x : St P) : Prop :=
  GridPin (Dof x) x.m.z.R.toRealDat.toLevCh K.C.P.CF K.s.b

variable (hL : GlobalTheory.Published.LocalLanglandsGL)

def NEc : NExt hL := fun K B f T w Z Wt p0 t nch n xd c => NEb hL K B f T w Z Wt p0 t nch n xd c ×
  PLift (GridPin (w.st Z).toD7 t.r.z.R.toRealDat.toLevCh K.C.P.CF K.s.b)

def NEcg : NExt hL := fun K B f T w Z Wt p0 t nch n xd c => NEc hL K B f T w Z Wt p0 t nch n xd c × PLift (GoodO (w.D Z) nch xd)

def SettingsFormsExistGrid : Prop := AllSt fun _ _ _ _ _ P x => LI hL x → ∃ x' : St P, Nonempty (SettingsLevel hL x') ∧ GridSt x'

def SeriesExistGrid : Prop := AllSt fun _ _ _ _ _ P x => SettingsLevel hL x → ∃ x' : St P, Nonempty (SeriesLevel hL x') ∧ (GridSt x → GridSt x')

def ModuliPointsExistGrid : Prop := AllSt fun _ _ _ _ _ P x => SeriesLevel hL x → ∃ x' : St P, Nonempty (StrictHenselianAcyclic hL x') ∧ (GridSt x → GridSt x')

def SFing : Prop := AllSt fun K _ _ _ w P x => ∀ (l : LC hL x) (S : SExt) (Γ : GeoP), GridSt x →
  ∃ (Z : w.Lt) (v : Lv3 (prmR (NEc hL) S Γ).s K w Z), v.Wt = P.Wt ∧ Kept l.c.ch v.nch

def SecondNg : Prop := ∀ (S : SExt) (Γ : GeoP), Pass KPx (IsBuiltE (prmR (NEc hL) S Γ).s) fun K B f T =>
  ∃ w : ColW B f T, Start K B f T w ∧ Has3 (prmR (NEcg hL) S Γ).s K B f T w

end GlobalTheory.HeightCounting.Up

end
