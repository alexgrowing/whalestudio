import Formalism.SharpRestriction.GrowthBounds.ChartedClasses.ClsChartedLabAt

noncomputable section

namespace Formalism.MainNotions.G.KAat

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.MainNotions.G.CmpJ

variable {D : D7} {c : LatCmp D} {Tw : TwForms D} {u : D.what₂.Word} {μ : D.what₂.Tup} {w : D.what₂.places.Pl}
  {h : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)} {Fl : Fills (D.gat u w h)} {Lv : Levels Fl}
  {I : CmpJIn Tw u μ w h Lv}

def tieAt (X : LabIn I) (H : CmpJHyp c I) (Gt : GatTies D) :
    TieAt c Tw u μ w h (chainAt H Gt) Formalism.L2.G.RelativeIndexFlags.blockRationality_holds Gt where
  lab := labAt X H
  inp := I
  hyp := H
  ch := (kaAt X H Gt).cmp_K

variable {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {K : G.Consts} {Dx : DivX D} {cX : ExtraC}

structure ChFam (E : Extra D L hT Gi Gl K Dx cX) where
  Lv : ∀ (_ : D.what₂.Tup) u (w : D.what₂.places.Pl) (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)), Levels (Gl.Fl u w hg)
  I : ∀ (μ : D.what₂.Tup), DV.Used D μ → ∀ u (w : D.what₂.places.Pl) (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)),
    D.what₂.places.resChar w ∉ Dx.Qp μ → CmpJIn E.tw u μ w hg (Lv μ u w hg)
  H : ∀ μ hU u w hg hq, CmpJHyp E.cmp (I μ hU u w hg hq)
  X : ∀ μ hU u w hg hq, LabIn (I μ hU u w hg hq)

open Classical in

def ChFam.ch {E : Extra D L hT Gi Gl K Dx cX} (F : ChFam E) (μ : D.what₂.Tup) (u : D.what₂.Word) (w : D.what₂.places.Pl)
    (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) : Chain (F.Lv μ u w hg) :=
  if hh : DV.Used D μ ∧ D.what₂.places.resChar w ∉ Dx.Qp μ then chainAt (F.H μ hh.1 u w hg hh.2) hT else ⟨fun _ => 0⟩

theorem ChFam.ch_eq {E : Extra D L hT Gi Gl K Dx cX} (F : ChFam E) (μ : D.what₂.Tup) (hU : DV.Used D μ) (u : D.what₂.Word)
    (w : D.what₂.places.Pl) (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) (hq : D.what₂.places.resChar w ∉ Dx.Qp μ) :
    F.ch μ u w hg = chainAt (F.H μ hU u w hg hq) hT := dif_pos ⟨hU, hq⟩

def ChFam.LC {E : Extra D L hT Gi Gl K Dx cX} (F : ChFam E) : D.what₂.Tup → ∀ u (w : D.what₂.places.Pl)
    (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)), Σ Lv : Levels (Gl.Fl u w hg), Chain Lv :=
  fun μ u w hg => ⟨F.Lv μ u w hg, F.ch μ u w hg⟩

def ChFam.ka {E : Extra D L hT Gi Gl K Dx cX} (F : ChFam E) (μ : D.what₂.Tup) (hU : DV.Used D μ) (u : D.what₂.Word)
    (w : D.what₂.places.Pl) (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) (hq : D.what₂.places.resChar w ∉ Dx.Qp μ) :
    TwTie.KerAtMu D E.cmp E.tw u μ w hg (F.ch μ u w hg) :=
  kaAtAny (F.X μ hU u w hg hq) (F.H μ hU u w hg hq) hT (F.ch μ u w hg) (by
    rw [F.ch_eq μ hU u w hg hq]
    exact (kaAt (F.X μ hU u w hg hq) (F.H μ hU u w hg hq) hT).cmp_K)

def ChFam.tied {E : Extra D L hT Gi Gl K Dx cX} (F : ChFam E) (e0 : ∀ u, E.tw.e0 u D.what₂.mu0 = E.tw.eMu0 u 0 (Nat.zero_le _)) :
    TwTie.TwistedUnitaryExtraData E where
  LC := F.LC
  ker := fun μ hU u w hg hq => F.ka μ hU u w hg hq
  twisted_e0_at_mu0_eq_eMu0 := e0

theorem ChFam.tied_Lv {E : Extra D L hT Gi Gl K Dx cX} (F : ChFam E) (e0) (μ : D.what₂.Tup) (u : D.what₂.Word) (w : D.what₂.places.Pl)
    (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) :
    ((Pk.reW Gl (F.tied e0).LC).Yt μ).Lv u w hg = F.Lv μ u w hg := rfl

theorem ChFam.tied_Ch {E : Extra D L hT Gi Gl K Dx cX} (F : ChFam E) (e0) (μ : D.what₂.Tup) (u : D.what₂.Word) (w : D.what₂.places.Pl)
    (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) :
    ((Pk.reW Gl (F.tied e0).LC).Yt μ).Ch u w hg = F.ch μ u w hg := rfl

theorem ChFam.tied_cls {E : Extra D L hT Gi Gl K Dx cX} (F : ChFam E) (e0) (μ : D.what₂.Tup) (hU : DV.Used D μ) (u : D.what₂.Word)
    (w : D.what₂.places.Pl) (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) (hq : D.what₂.places.resChar w ∉ Dx.Qp μ) :
    ((F.tied e0).ker μ hU u w hg hq).cls = clsAt (F.X μ hU u w hg hq) (F.H μ hU u w hg hq) := rfl

theorem ChFam.tied_cmp {E : Extra D L hT Gi Gl K Dx cX} (F : ChFam E) (e0) (μ : D.what₂.Tup) (hU : DV.Used D μ) (u : D.what₂.Word)
    (w : D.what₂.places.Pl) (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) (hq : D.what₂.places.resChar w ∉ Dx.Qp μ)
    (j : ℕ) (hj : j + 1 ≤ D.R.m) (x : ((E.tw.fm u μ).lat (j + 1)).V) :
    ((F.tied e0).ker μ hU u w hg hq).cmp (j + 1) x =
      ((F.I μ hU u w hg hq).at' j hj).st.cmpJ (E.cmp.embW u w hg) (((F.I μ hU u w hg hq).at' j hj).eps.symm x) :=
  kaAt_cmp (F.X μ hU u w hg hq) (F.H μ hU u w hg hq) hT j hj x

end Formalism.MainNotions.G.KAat

end
