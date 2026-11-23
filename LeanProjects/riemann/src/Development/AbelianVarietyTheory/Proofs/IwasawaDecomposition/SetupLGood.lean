import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TwistDataAgreeAcrossCoefficientsLocalized

noncomputable section

namespace GlobalTheory.HeightCounting.Fin3

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top
  GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up

attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 4000000

variable {hL : GlobalTheory.Published.LocalLanglandsGL} {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} {P : Pre2 K w}
variable {x : St P} (L : LocAll (lay0 (Dof x)))

def twL {A : Type} [CommGroup A] (t : GlobalTheory.ExportSeries.Twist (Dof x) A) : GlobalTheory.ExportSeries.Twist (DL x L) A :=
  ⟨(by with_unfolding_all exact (t.Q :)), (by with_unfolding_all exact (t.chi :)), (by with_unfolding_all exact (t.res :))⟩

def twB {A : Type} [CommGroup A] (t : GlobalTheory.ExportSeries.Twist (DL x L) A) : GlobalTheory.ExportSeries.Twist (Dof x) A :=
  ⟨(by with_unfolding_all exact (t.Q :)), (by with_unfolding_all exact (t.chi :)), (by with_unfolding_all exact (t.res :))⟩

def frL {S U : Formalism.BasicNotions.TH.HSp (Dof x)} (F : GlobalTheory.ExportSeries.Frame S U) : @GlobalTheory.ExportSeries.Frame (DL x L) ((S)) ((U)) where
  ψ := (by with_unfolding_all exact (F.ψ :))
  θ := (by with_unfolding_all exact (F.θ :))
  sT := (by with_unfolding_all exact (F.sT :))
  BS := (by with_unfolding_all exact (F.BS :))
  BT := (by with_unfolding_all exact (F.BT :))
  ΛS := (by with_unfolding_all exact (F.ΛS :))
  ΛT := (by with_unfolding_all exact (F.ΛT :))
  βS := (by with_unfolding_all exact (F.βS :))
  βT := (by with_unfolding_all exact (F.βT :))
  f₀ := (by with_unfolding_all exact (F.f₀ :))

def tdL {r : ℕ} (G : GlobalTheory.ExportSeries.TypeDat (Dof x) r) : GlobalTheory.ExportSeries.TypeDat (DL x L) r := ⟨(by with_unfolding_all exact (G.Pg :)), (by with_unfolding_all exact (G.P :)), (by with_unfolding_all exact (G.mu :))⟩

def wtL {n : ℕ} (u : GlobalTheory.ExportSeries.Weight (Dof x) n) : GlobalTheory.ExportSeries.Weight (DL x L) n :=
  ⟨(by with_unfolding_all exact (u.p :)), (by with_unfolding_all exact (u.q :)), (by with_unfolding_all exact (u.ap :)), (by with_unfolding_all exact (u.am :)), (by with_unfolding_all exact (u.c :)), (by with_unfolding_all exact (u.lam :))⟩

def baseL {S U : Formalism.BasicNotions.TH.HSp (Dof x)} (Z : GlobalTheory.ExportSeries.Base S U) : @GlobalTheory.ExportSeries.Base (DL x L) ((S)) ((U)) where
  hr := (by with_unfolding_all exact (Z.hr :))
  F := frL L Z.F
  G := (by with_unfolding_all exact ((tdL L Z.G) :))
  de := twL L Z.de
  w := (by with_unfolding_all exact ((wtL L Z.w) :))
  mu0 := (by with_unfolding_all exact (Z.mu0 :))
  eta := (by with_unfolding_all exact (Z.eta :))

def setupL (ρ : GlobalTheory.SeriesTie.Setup (Dof x).ntw) : GlobalTheory.SeriesTie.Setup (DL x L).ntw where
  rc := ⟨(by with_unfolding_all exact (ρ.rc.κ :)), (by with_unfolding_all exact (ρ.rc.art :))⟩
  ch := (by with_unfolding_all exact (ρ.ch :))
  bad := (by with_unfolding_all exact (ρ.bad :))
  e := (by with_unfolding_all exact (ρ.e :))
  ek := (by with_unfolding_all exact (ρ.ek :))
  B := fun i j b => (by with_unfolding_all exact ((baseL L (ρ.B ((i)) ((j)) b)) : _))
  om := fun i j b χ => (by with_unfolding_all exact ((ρ.om ((i)) ((j)) b ((χ))) : _))
  Cl := fun i j b t => ρ.Cl ((by with_unfolding_all exact (i :))) ((by with_unfolding_all exact (j :))) b (twB L t)
  finCl := fun i j b t => ρ.finCl ((by with_unfolding_all exact (i :))) ((by with_unfolding_all exact (j :))) b (twB L t)
  rep := fun i j b t c => (by with_unfolding_all exact ((ρ.rep ((i)) ((j)) b (twB L t) c) : _))
  β := (by with_unfolding_all exact (ρ.β :))
  eG := (by with_unfolding_all exact (ρ.eG :))

theorem twL_good {A : Type} [CommGroup A] {t : GlobalTheory.ExportSeries.Twist (Dof x) A} (h : t.Good) : (twL L t).Good :=
  ⟨(by with_unfolding_all exact (h.isOpen :)), (by with_unfolding_all exact (h.rat :)), (by with_unfolding_all exact (h.real :)), (by with_unfolding_all exact (h.split :)), (by with_unfolding_all exact (h.unram :)), (by with_unfolding_all exact (h.res :))⟩

theorem twB_good {A : Type} [CommGroup A] {t : GlobalTheory.ExportSeries.Twist (DL x L) A} (h : t.Good) : (twB L t).Good :=
  ⟨(by with_unfolding_all exact (h.isOpen :)), (by with_unfolding_all exact (h.rat :)), (by with_unfolding_all exact (h.real :)), (by with_unfolding_all exact (h.split :)), (by with_unfolding_all exact (h.unram :)), (by with_unfolding_all exact (h.res :))⟩

theorem placesOK_L {Pg Q : Finset (HeightOneSpectrum (𝓞 (Dof x).host.E))} (h : @GlobalTheory.ExportSeries.PlacesOK (Dof x) Pg Q) :
    @GlobalTheory.ExportSeries.PlacesOK (DL x L) ((Pg)) ((Q)) := ⟨(h.split), (h.disj), (h.prime)⟩

theorem placesOK_B {Pg Q : Finset (HeightOneSpectrum (𝓞 (DL x L).host.E))} (h : @GlobalTheory.ExportSeries.PlacesOK (DL x L) Pg Q) :
    @GlobalTheory.ExportSeries.PlacesOK (Dof x) ((Pg)) ((Q)) := ⟨(h.split), (h.disj), (h.prime)⟩

theorem wtL_good {n : ℕ} {u : GlobalTheory.ExportSeries.Weight (Dof x) n} (h : u.Good) : (wtL L u).Good := ⟨(by with_unfolding_all exact (h.le :)), (by with_unfolding_all exact (h.lam_eq :))⟩

theorem frL_good {S U : Formalism.BasicNotions.TH.HSp (Dof x)} {F : GlobalTheory.ExportSeries.Frame S U} (h : F.Good) : (frL L F).Good :=
  { rank_le := (by with_unfolding_all exact (h.rank_le :))
    onbS := (by with_unfolding_all exact (h.onbS :))
    cartT := (by with_unfolding_all exact (h.cartT :))
    onbT := (by with_unfolding_all exact (h.onbT :))
    sdS := (by with_unfolding_all exact (h.sdS :))
    sdT := (by with_unfolding_all exact (h.sdT :))
    frS := (by with_unfolding_all exact (h.frS :))
    frT := (by with_unfolding_all exact (h.frT :))
    vac := by tr_clause x.o.Z (oL x L).Z h.vac }

theorem baseL_good {S U : Formalism.BasicNotions.TH.HSp (Dof x)} {Z : GlobalTheory.ExportSeries.Base S U} (h : Z.Good) : (baseL L Z).Good :=
  { even := (by with_unfolding_all exact (h.even :))
    odd := (by with_unfolding_all exact (h.odd :))
    frame := frL_good L h.frame
    de := twL_good L h.de
    places := (by with_unfolding_all exact ((placesOK_L L h.places) :))
    wt := (by with_unfolding_all exact ((wtL_good L h.wt) :))
    sig := (by with_unfolding_all exact (h.sig :))
    sigOK := (by with_unfolding_all exact (h.sigOK :))
    eta := (by with_unfolding_all exact (h.eta :))
    hecke := (by with_unfolding_all exact (h.hecke :))
    real := (by with_unfolding_all exact (h.real :))
    unram := (by with_unfolding_all exact (h.unram :))
    tame := (by with_unfolding_all exact (h.tame :))
    inf := (by with_unfolding_all exact (h.inf :)) }

theorem setupL_good {ρ : GlobalTheory.SeriesTie.Setup (Dof x).ntw} (h : ρ.Good) : (setupL L ρ).Good :=
  { rc := ⟨(by with_unfolding_all exact (h.rc.cont :)), (by with_unfolding_all exact (h.rc.rat :)), (by with_unfolding_all exact (h.rc.loc :)), (by with_unfolding_all exact (h.rc.artin :))⟩
    ch := fun i => ⟨(by with_unfolding_all exact ((h.ch ((i))).pair : _)), (by with_unfolding_all exact ((h.ch ((i))).one : _))⟩
    bad_ne := (by with_unfolding_all exact (h.bad_ne :))
    goodSetup_bad_mem_badPlaces := (by with_unfolding_all exact (h.goodSetup_bad_mem_badPlaces :))
    goodSetup_badPlaces_conj := (by with_unfolding_all exact (h.goodSetup_badPlaces_conj :))
    goodSetup_placesOverTwo_subset := (by with_unfolding_all exact (h.goodSetup_placesOverTwo_subset :))
    goodSetup_count_eq_zero_off_badPlaces := (by with_unfolding_all exact (h.goodSetup_count_eq_zero_off_badPlaces :))
    e_LL0 := (by with_unfolding_all exact (h.e_LL0 :))
    ek_e := (by with_unfolding_all exact (h.ek_e :))
    base := fun i j b => (by with_unfolding_all exact ((baseL_good L (h.base ((i)) ((j)) b)) : _))
    latS := (by with_unfolding_all exact (h.latS :))
    latT := (by with_unfolding_all exact (h.latT :))
    Pg := (by with_unfolding_all exact (h.Pg :))
    delta := fun i j b => kc% (congrArg (twL L) (h.delta (kc% i) (kc% j) b))
    weil := fun i j b t ht => by
      delta GlobalTheory.ExportSeries.Base.IsWeil
      tr_leaves x.o.Z (oL x L).Z
      exact (by with_unfolding_all exact ((h.weil ((i)) ((j)) b (twB L t) (twB_good L ht)) : _))
    classes := fun i j b t ht hA =>
      have h' := h.classes ((by with_unfolding_all exact (i :))) ((by with_unfolding_all exact (j :))) b (twB L t) (twB_good L ht) ⟨(by with_unfolding_all exact ((placesOK_B L hA.1) :)), (by with_unfolding_all exact (hA.2 :))⟩
      ⟨(by with_unfolding_all exact (h'.fin :)), (by with_unfolding_all exact (h'.reps :)), (by with_unfolding_all exact (h'.stab :))⟩ }

theorem pinL (l : LC hL x) : GlobalTheory.SeriesTie.RealPin (datL x L).R (datL x L).cG (setupL L l.b.ser.ex.ρ) :=
  have p := l.b.ser.ex.pin
  ⟨(by with_unfolding_all exact (p.psi :)), (by with_unfolding_all exact (p.inf :)), (by with_unfolding_all exact (p.cartT :)), (by with_unfolding_all exact (p.onbS :)), (by with_unfolding_all exact (p.onbT :)), (by with_unfolding_all exact (p.latS :)), (by with_unfolding_all exact (p.latT :)), (by with_unfolding_all exact (p.frS :)), (by with_unfolding_all exact (p.frT :)), (by with_unfolding_all exact (p.vac :)), (by with_unfolding_all exact (p.Pg :)),
    (by with_unfolding_all exact (p.grp :)), (by with_unfolding_all exact (p.mu0 :)), (by with_unfolding_all exact (p.eta :)), (by with_unfolding_all exact (p.delta :)), (by with_unfolding_all exact (p.deltaPl :)), (by with_unfolding_all exact (p.ap :)), (by with_unfolding_all exact (p.am :))⟩

theorem univL (l : LC hL x) : GlobalTheory.UnivChar.IsUnivChar (DL x L).nexp := (by with_unfolding_all exact (l.b.ser.ex.univ :))

open GlobalTheory.SeriesTie in

theorem theta_eq (ρ : Setup (Dof x).ntw) :
    (setupL L ρ).theta = fun i j b h P => (by exact ρ.theta i j b h P) := by
  funext i j b h P
  delta GlobalTheory.SeriesTie.Setup.theta GlobalTheory.ExportSeries.Base.theta GlobalTheory.ExportSeries.Base.vecBase GlobalTheory.ExportSeries.Base.vecAt
    GlobalTheory.ExportSeries.Frame.vec GlobalTheory.ExportSeries.Frame.placeMap
  tr_leaves x.o.Z (oL x L).Z
  kexactB (Eq.refl (ρ.theta (kc% i) (kc% j) b (kc% h) (kc% P)))

open GlobalTheory.SeriesTie in

theorem isDatum_eq (ρ : Setup (Dof x).ntw) :
    (setupL L ρ).IsDatum = fun i j b s h P => (by exact ρ.IsDatum i j b s h P) := by
  funext i j b s h P
  refine propext ⟨fun d => ?_, fun d => ?_⟩
  · exact (by with_unfolding_all exact ((⟨(d.split), (d.off), (d.fin), (d.supp), (d.mem)⟩ : ρ.IsDatum ((i)) ((j)) b ((s)) ((h)) ((P))) : _))
  · exact ⟨(by with_unfolding_all exact (d.split :)), (by with_unfolding_all exact (d.off :)), (by with_unfolding_all exact (d.fin :)), (by with_unfolding_all exact (d.supp :)), (by with_unfolding_all exact (d.mem :))⟩

end GlobalTheory.HeightCounting.Fin3

end
