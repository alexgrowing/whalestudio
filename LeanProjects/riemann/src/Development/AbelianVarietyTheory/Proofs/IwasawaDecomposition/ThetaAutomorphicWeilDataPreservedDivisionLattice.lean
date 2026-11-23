import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ColumnLocalDataTransportDivision
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.Db GlobalTheory.Mem.Top.Bl.WitTr NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 4000000

namespace GlobalTheory.Mem.Top.Bl.ThTTr

open Formalism.L2.Theta Formalism.L2.JoinChr
open scoped TensorProduct
open Formalism.BasicNotions.TH (tauE)

section Gen

variable {D : D7} (N : ∀ u, Submodule (𝓞 D.what₂.LL) (D.div.Nu u).V) (h : D.what₂.Word → ℝ)

theorem isAutFun_tr {V : TH.HSp D} {φ : GA D V → ℂ} :
    IsAutFun (D := D) V φ ↔ IsAutFun (D := setDiv D N h) V φ :=
  ⟨fun x => ⟨x.left, x.level, x.cont⟩, fun x => ⟨x.left, x.level, x.cont⟩⟩

theorem isAutFunSm_tr {θ : D.what₂.Tau → (GlobalTheoryTheory.GenusMassVolumes.Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)} {V : TH.HSp D}
    {φ : GA D V → ℂ} : IsAutFunSm (D := D) θ V φ ↔ IsAutFunSm (D := setDiv D N h) θ V φ :=
  ⟨fun x => ⟨(isAutFun_tr N h).1 x.toIsAutFun, x.smooth, x.zfin, x.growth⟩,
   fun x => ⟨(isAutFun_tr N h).2 x.toIsAutFun, x.smooth, x.zfin, x.growth⟩⟩

theorem isThetaFun_tr {ψ : AddChar (GlobalTheoryTheory.GenusMassVolumes.AF D.host.F) ℂ} {V W : TH.HSp D} {f : WA V W → ℂ} :
    IsThetaFun (D := D) ψ V W f ↔ IsThetaFun (D := setDiv D N h) ψ V W f :=
  ⟨fun x => ⟨x.quasi, x.level, x.cont, x.smooth⟩, fun x => ⟨x.quasi, x.level, x.cont, x.smooth⟩⟩

theorem isPolFock_tr {ψ : AddChar (GlobalTheoryTheory.GenusMassVolumes.AF D.host.F) ℂ}
    {θ : D.what₂.Tau → (GlobalTheoryTheory.GenusMassVolumes.Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)} {V W : TH.HSp D}
    {A : ∀ τ : D.what₂.Tau, Matrix (Fin (V.sig (tauE D τ)).1 ⊕ Fin (V.sig (tauE D τ)).2) (Fin V.rank) ℂ}
    {B : ∀ τ : D.what₂.Tau, Matrix (Fin (W.sig (tauE D τ)).1 ⊕ Fin (W.sig (tauE D τ)).2) (Fin W.rank) ℂ}
    {f : WA V W → ℂ} :
    IsPolFock (D := D) ψ θ V W A B f ↔ IsPolFock (D := setDiv D N h) ψ θ V W A B f :=
  ⟨fun ⟨J, x, rest⟩ => ⟨J, ⟨x.cont, x.real, x.sq, x.symp, x.kcomm, x.defin⟩, rest⟩,
   fun ⟨J, x, rest⟩ => ⟨J, ⟨x.cont, x.real, x.sq, x.symp, x.kcomm, x.defin⟩, rest⟩⟩

@[reducible] def besDatTr {A B : TH.HSp D} {ι : A.V →ₗ[D.host.E] B.V} (d : BesDat (D := D) A B ι) :
    BesDat (D := setDiv D N h) A B ι := { d with }

set_option maxHeartbeats 4000000 in

def thetaTiedTr {X : ThetaX D} (T : ThetaTied D X) : ThetaTied (setDiv D N h) (thTr N h X) :=
  { T with ev_aut := fun V F => (isAutFun_tr N h).1 (T.ev_aut V F) }

set_option maxHeartbeats 4000000 in

def weilTiedTr {X : ThetaX D} {T : ThetaTied D X} (Wl : WeilTied D X T) :
    WeilTied (setDiv D N h) (thTr N h X) (thetaTiedTr N h T) :=
  { Wl with
    evS_range := fun V W hne => (Wl.evS_range V W hne).trans (Set.ext fun _ => isThetaFun_tr N h)
    om_tw := { Wl.om_tw with } }

set_option maxHeartbeats 4000000 in

theorem weilTiedEq_tr {X : ThetaX D} {T : ThetaTied D X} {Wl : WeilTied D X T} (e : WeilCompatibleEquivariance Wl) :
    WeilCompatibleEquivariance (weilTiedTr N h Wl) :=
  { e with
    evS_range := fun V W hr => (e.evS_range V W hr).trans (Set.ext fun _ => isThetaFun_tr N h)
    om_tw := { e.om_tw with } }

set_option maxHeartbeats 4000000 in

def allTiedTr {X : ThetaX D} {A : TH.ProvA} (a : AllTied D X A) : AllTied (setDiv D N h) (thTr N h X) A where
  T := thetaTiedTr N h a.T
  sm := ⟨a.sm.1, fun θ hθ V hV => (a.sm.2 θ hθ V hV).trans (Set.ext fun _ => isAutFunSm_tr N h)⟩
  ty := { a.ty with }
  W := weilTiedTr N h a.W
  unr := a.unr
  kf := { a.kf with
    kfin := ⟨a.kf.kfin.1, fun θ hθ V W h1 h2 h3 Φ => (a.kf.kfin.2 θ hθ V W h1 h2 h3 Φ).trans (isPolFock_tr N h)⟩ }
  phiUp := a.phiUp
  B := { a.B with dat := fun A B ι ho p => besDatTr N h (a.B.dat A B ι ho p) }
  real := { a.real with }
  prov := { a.prov with }

end Gen

end GlobalTheory.Mem.Top.Bl.ThTTr

open GlobalTheory.Mem.Top.Bl.ThTTr in
set_option maxHeartbeats 16000000 in

theorem GlobalTheory.Mem.Top.Bl.ThTTr.thT_setDiv : ∀ {B : Base} {f : Fr B.toPre} {T : TwDat B} (w : ColW B f T) (Z : w.Lt) {Wt : Set B.places.Pl} {nch : NChoice (w.D Z)} (n : NchT w Z Wt nch) (th : ThetaX (w.D Z)) (N : ∀ u, Submodule (𝓞 B.LL) (Z.V.div.Nu u).V) (h : B.Word → ℝ), ThT n th → Nonempty (ThT (nchTTr w Z N h n) (thTr (D := w.D Z) N h th)) := by
  intro B f T w Z Wt nch n th N h t
  exact ⟨{ provA := t.provA
           all := allTiedTr (D := w.D Z) N h t.all
           weq := weilTiedEq_tr (D := w.D Z) N h t.weq
           chr := { t.chr with }
           same := { t.same with }
           std := t.std
           io := t.io }⟩
