import Mathlib
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.SetUnipotentTranslate

noncomputable section

namespace GlobalTheory.Mem.Top

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.FrobeniusOrbits GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem NumberField

structure Obj2 (D : D7) : Type 1 where

  gatT : GatTies D

  th : ThetaX D

  cmp : LatCmp D

  tw : TwForms D

  Gy : G.LatInst D

  errX : ErrX D

  nch : NChoice D

  xd : ThData D

  lev : LevelData D

  X : DivX D

  p0 : BaseLevelRowSide D

  ker : ∀ u w (h : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)),
    haveI : Fact (D.what₂.places.resChar w).Prime := ⟨D.what₂.places.resChar_prime w⟩
    LocalToGlobal₂ D gatT cmp tw u w h (Gy.Ch u w h)

  amb : AmbForm D (RowSide.sharp D)

  amb0 : AmbForm D p0.s

  gauge : letI := D.host.cmStar; GlobalTheoryTheory.GenusMassVolumes.GaugeFam D.host.F D.host.E D.sp.cm.sig

def layObj {D : D7} (Y : Lay D) : Obj2 D := { Y with }

def divXtr {D : D7} (X : DivX D) (N : ∀ u, Submodule (𝓞 D.what₂.LL) (D.div.Nu u).V) (h : D.what₂.Word → ℝ) : DivX (setDiv D N h) :=
  divTr N h X

def Obj2.tr {D : D7} (O : Obj2 D) (N : ∀ u, Submodule (𝓞 D.what₂.LL) (D.div.Nu u).V) (h : D.what₂.Word → ℝ) : Obj2 (setDiv D N h) where
  gatT := gatTr N h O.gatT
  th := thTr N h O.th
  cmp := cmpTr N h O.cmp
  tw := twTr N h O.tw
  Gy := latTr N h O.Gy
  errX := errTr N h O.errX
  nch := nchTr N h O.nch
  xd := xdTr N h O.xd
  lev := O.lev
  X := divTr N h O.X
  p0 := ⟨sideTr N h O.p0.s⟩
  ker := fun u w g => { O.ker u w g with }
  amb := { O.amb with }
  amb0 := { O.amb0 with }
  gauge := O.gauge

def pointPropertyOfObjects (QO : ∀ D : D7, Obj2 D → Prop) : PtProp := fun D _ gatT _ Gy _ X _ ex =>
  QO D { gatT := gatT, th := ex.th, cmp := ex.cmp, tw := ex.tw, Gy := Gy, errX := ex.errX, nch := ex.nch, xd := ex.xd,
         lev := ex.lev, X := X, p0 := ex.p0, ker := ex.ker, amb := ex.amb, amb0 := ex.amb0, gauge := ex.gauge }

def allDiv (QO : ∀ D : D7, Obj2 D → Prop) (D : D7) (Y : Lay D) : Prop := ∀ N h, QO (setDiv D N h) ((layObj Y).tr N h)

def extraObj {D : D7} {L : SizeData₂ D} {gatT : GatTies D} {Gx : G.Inst D L} {Gy : G.LatInst D} {K : G.Consts} {X : DivX D}
    {cX : ExtraC} (ex : Extra D L gatT Gx Gy K X cX) : Obj2 D :=
  { gatT := gatT, th := ex.th, cmp := ex.cmp, tw := ex.tw, Gy := Gy, errX := ex.errX, nch := ex.nch, xd := ex.xd,
    lev := ex.lev, X := X, p0 := ex.p0, ker := ex.ker, amb := ex.amb, amb0 := ex.amb0, gauge := ex.gauge }

def ofObj {D : D7} (O : Obj D) : Obj2 D := extraObj O.ex

def pointObj {C : FC} (p : Pt C) : Obj2 p.D := extraObj p.xa.ex

theorem has_pointProperty_iff {C : FC} (p : Pt C) (QO : ∀ D : D7, Obj2 D → Prop) : p.Has (pointPropertyOfObjects QO) ↔ QO p.D (pointObj p) := Iff.rfl

theorem pointPropertyOfObjects_eq_ptO (QO : ∀ D : D7, Obj2 D → Prop) : pointPropertyOfObjects QO = ptO (fun D O => QO D (ofObj O)) := rfl

theorem ofObj_ofPt {C : FC} (p : Pt C) : ofObj (Obj.ofPt p) = pointObj p := rfl

theorem ofObj_obj {C : FC} {D : D7} (Y : Lay D) (p : LedPart C Y) : ofObj (Y.obj p) = layObj Y := rfl

theorem ofObj_tr {D : D7} (O : Obj D) (N : ∀ u, Submodule (𝓞 D.what₂.LL) (D.div.Nu u).V) (h : D.what₂.Word → ℝ) :
    ofObj (O.tr N h) = (ofObj O).tr N h := rfl

theorem layObj_ofPt {C : FC} (p : Pt C) : layObj (Lay.ofPt p) = pointObj p := rfl

theorem layObj_injective {D : D7} : Function.Injective (layObj (D := D)) := by
  intro Y Y' H
  cases Y; cases Y'
  cases H
  rfl

theorem pointObj_pt {C : FC} {D : D7} {Y : Lay D} (p : LedPart C Y) : pointObj p.pt = (layObj Y).tr (nPrime p.L) p.ht := rfl

theorem allDiv.has_pt {QO : ∀ D : D7, Obj2 D → Prop} {C : FC} {D : D7} {Y : Lay D} (H : allDiv QO D Y) (p : LedPart C Y) :
    p.pt.Has (pointPropertyOfObjects QO) := H _ _

theorem allDiv.ofPt_pt {QO : ∀ D : D7, Obj2 D → Prop} {C : FC} {D : D7} {Y : Lay D} (H : allDiv QO D Y) (p : LedPart C Y) :
    QO p.pt.D (ofObj (Obj.ofPt p.pt)) := H _ _

theorem Obj2.tr_X {D : D7} (O : Obj2 D) (N : ∀ u, Submodule (𝓞 D.what₂.LL) (D.div.Nu u).V) (h : D.what₂.Word → ℝ) :
    (O.tr N h).X = divXtr O.X N h := rfl

theorem Obj2.tr_tr {D : D7} (O : Obj2 D) (N N' : ∀ u, Submodule (𝓞 D.what₂.LL) (D.div.Nu u).V) (h h' : D.what₂.Word → ℝ) :
    (O.tr N h).tr N' h' = O.tr N' h' := rfl

theorem pointProperty_and (Q Q' : ∀ D : D7, Obj2 D → Prop) : pointPropertyOfObjects (fun D O => Q D O ∧ Q' D O) = (pointPropertyOfObjects Q).and (pointPropertyOfObjects Q') := rfl

theorem allDiv_and_iff (Q Q' : ∀ D : D7, Obj2 D → Prop) (D : D7) (Y : Lay D) :
    allDiv (fun D O => Q D O ∧ Q' D O) D Y ↔ allDiv Q D Y ∧ allDiv Q' D Y :=
  ⟨fun H => ⟨fun N h => (H N h).1, fun N h => (H N h).2⟩, fun H N h => ⟨H.1 N h, H.2 N h⟩⟩

theorem allDiv_mono {Q Q' : ∀ D : D7, Obj2 D → Prop} (hQ : ∀ D O, Q D O → Q' D O) {D : D7} {Y : Lay D} (H : allDiv Q D Y) :
    allDiv Q' D Y := fun N h => hQ _ _ (H N h)

theorem nonempty_objects_iff (D : D7) : Nonempty (Obj2 D) ↔
    Nonempty (ThetaX D) ∧ Nonempty (ErrX D) ∧ Nonempty (NChoice D) ∧ Nonempty (ThData D) ∧
      Nonempty (LevelData D) ∧ Nonempty (DivX D) ∧ (∃ P : BaseLevelRowSide D, Nonempty (AmbForm D P.s)) ∧
      Nonempty (AmbForm D (RowSide.sharp D)) ∧
      Nonempty (letI := D.host.cmStar; GlobalTheoryTheory.GenusMassVolumes.GaugeFam D.host.F D.host.E D.sp.cm.sig) ∧
      ∃ (gatT : GatTies D) (cmp : LatCmp D) (tw : TwForms D) (Gy : G.LatInst D),
        Nonempty (∀ u w (h : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)),
          haveI : Fact (D.what₂.places.resChar w).Prime := ⟨D.what₂.places.resChar_prime w⟩
          LocalToGlobal₂ D gatT cmp tw u w h (Gy.Ch u w h)) :=
  ⟨fun ⟨O⟩ => ⟨⟨O.th⟩, ⟨O.errX⟩, ⟨O.nch⟩, ⟨O.xd⟩, ⟨O.lev⟩, ⟨O.X⟩, ⟨O.p0, ⟨O.amb0⟩⟩, ⟨O.amb⟩, ⟨O.gauge⟩,
      O.gatT, O.cmp, O.tw, O.Gy, ⟨O.ker⟩⟩,
    fun ⟨⟨th⟩, ⟨e⟩, ⟨n⟩, ⟨xd⟩, ⟨a⟩, ⟨b⟩, ⟨c, ⟨c0⟩⟩, ⟨d⟩, ⟨g⟩, gt, cm, tw, Gy, ⟨k⟩⟩ =>
      ⟨⟨gt, th, cm, tw, Gy, e, n, xd, a, b, c, k, d, c0, g⟩⟩⟩

example {C : FC} (p : Pt C) (N : ∀ u, Submodule (𝓞 p.D.what₂.LL) (p.D.div.Nu u).V) (h : p.D.what₂.Word → ℝ) :
    Nonempty (Obj2 p.D) ∧ Nonempty (Obj2 (setDiv p.D N h)) :=
  ⟨⟨pointObj p⟩, ⟨(pointObj p).tr N h⟩⟩

example {C : FC} (p : Pt C) : (pointObj p).amb = p.xa.ex.amb ∧ (pointObj p).amb0 = p.xa.ex.amb0 ∧
    (pointObj p).gauge = p.xa.ex.gauge := ⟨rfl, rfl, rfl⟩

example {C : FC} (p : Pt C) :
    p.Has (pointPropertyOfObjects fun D O => LocalQuadraticParts.PeterssonBoundAllEmbeddings D O.X O.amb) ↔ LocalQuadraticParts.PeterssonBoundAllEmbeddings p.D p.xa.X p.xa.ex.amb := Iff.rfl

example {D : D7} (O : Obj2 D) (N : ∀ u, Submodule (𝓞 D.what₂.LL) (D.div.Nu u).V) (h : D.what₂.Word → ℝ) :
    (O.tr N h).amb.MtH = O.amb.MtH ∧ (O.tr N h).amb0.MtH = O.amb0.MtH ∧ (O.tr N h).gauge = O.gauge ∧
      (O.tr N h).X.kapR = O.X.kapR := ⟨rfl, rfl, rfl, rfl⟩

example (D : D7) (Y : Lay D) : allDiv (fun D O => letI := D.host.cmStar; O.gauge.IsGauge) D Y := fun _ _ => Y.gauge_def

example (D : D7) (Y : Lay D) : ¬ allDiv (fun D _ => D.div.h D.u₀ = 0) D Y := fun H =>
  one_ne_zero (H (fun u => (D.div.Nu u).L) (fun _ => 1))

end GlobalTheory.Mem.Top

end
