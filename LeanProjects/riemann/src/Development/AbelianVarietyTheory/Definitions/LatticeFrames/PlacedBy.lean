import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Framed
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.StageY
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam GlobalTheory.Core.Mi ValuativeRel
open Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowDict Formalism.L2.SG.PoincareInHH.PoincareSetting
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.LevZero

open GlobalTheory.ChainOnto (Com)

variable {D : D7}

section Common

variable {c : Comm D} {v : VCom c}

def Red (G : GLoc v) (PP : Formalism.L2.DIV.Pl D.host.E) (x : G.S.P.J) (g : GL (Fin D.R.r) (Formalism.L2.DIV.kP PP)) : Prop :=
  ∀ (a b : Fin D.R.k ⊕ Fin (G.s + 1)) (a' b' : Fin D.R.r), a'.val = GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.framePos _ _ a →
    b'.val = GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.framePos _ _ b → ∀ z : 𝓞 D.host.E, Ideal.Quotient.mk PP.asIdeal z = g.val a' b' →
      valuation G.k ((x : GL (Fin D.R.k ⊕ Fin (G.s + 1)) G.k).val a b - (ofSplit G.q).pr (z : D.host.E)) < 1

structure LocAt (G : GLoc v) (PP : Formalism.L2.DIV.Pl D.host.E) (b : GA D (c.V 0)) (β : GL (Fin (c.V 0).rank) (Lev.EAf D)) : Prop where
  idem : Formalism.L2.NTheta.IsIdemAt G.q.e PP
  under : G.q.v = PP.under (𝓞 D.host.F)
  frame : ∀ a (ha : 0 + a = G.s + 1), ∃ e : Ix (Fin D.R.k ⊕ Fin (G.s + 1)) (Fin D.R.t) 0 ≃ Fin (c.V 0).rank,
    GlobalTheory.SymBridge.IsOrd GlobalTheory.SymBridge.zPos e ∧ MovedTo (ofSplit G.q) (c.V 0) b β
      (((G.FY 0 a ha).β * ((G.S.T (Fin D.R.t)).bas 0 a ha).val).submatrix id
        fun i => stdOrd (Fin D.R.k) (Fin D.R.t) 0 a ha (e.symm i))

structure Bot (cm : Com D) (st : StAt (c.V 0)) (b : GA D (c.V 0)) (G : cm.Pg → GLoc v) : Prop where
  com : cm.Is
  psi : cm.ψ = c.ψ
  mem : st.st.Is cm 0
  fin : b ∈ GfC (c.V 0)
  typ : IsTypePlaces cm.Pg
  loc : ∀ PP : cm.Pg, LocAt (G PP) PP.1 b st.β
  grp : ∀ g : ∀ PP : cm.Pg, GL (Fin D.R.r) (Formalism.L2.DIV.kP PP.1), g ∈ cm.P.H ↔ ∀ PP, ∃ x, Red (G PP) PP.1 x (g PP)
  chr : ∀ (g : cm.P.H) (x : ∀ PP, (G PP).S.P.J), (∀ PP, Red (G PP) PP.1 (x PP) (g.1 PP)) →
    cm.P.chi g = ∏ PP, (G PP).S.P.lam (x PP)

end Common

variable {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX}

abbrev datZero (W : RealPack ex) : Formalism.L2.DIV.LevDat D.host.E ℂ (Yc D 0).rank :=
  W.Q.Rl.dat0 (W.Q.Rl.toRealDat.levR W.Q.F.lv2 true)

def stZero (W : RealPack ex) : StAt (Yc D 0) where
  par := (GlobalTheory.BaseChain.stageY W 0).par
  M := (GlobalTheory.BaseChain.stageY W 0).M
  Λ := (pk W).ΛY 0
  β := (pk W).βY 0
  L := datZero W
  ν := (GlobalTheory.BaseChain.stageY W 0).ν
  fd := (GlobalTheory.BaseChain.stageY W 0).fd

variable {W : RealPack ex} {u : D.what₂.Word}

structure PlacedBy (f : FamCh W u) (B : SBes W.S.X W.Q.instEq u W.Q.Rl.ψ (D.sp.X 0))
    {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {ι : Type}
    (v : VCom f.c) (o : TDat f.c k ι) {n : ℕ} (G : Fin n → GLoc v) (pl : Fin n ≃ (pk W).Pg) : Prop where
  cis : f.c.Is
  vis : v.Is
  tie : VTie f v
  shape : ShapeOff v o
  pin : GPin G
  read : GRead f G pl
  bot : BotTie f B v o G

set_option maxHeartbeats 1000000 in

def frAt (f : FamCh W u) (B : SBes W.S.X W.Q.instEq u W.Q.Rl.ψ (D.sp.X 0)) (a₀ a : GA D (D.sp.X 0)) :
    GL (Fin (D.sp.Y 0).rank) (Lev.EAf D) :=
  finE (D.sp.Y 0) (tOf f B a₀ a) * (show GL (Fin (D.sp.Y 0).rank) (Lev.EAf D) from (pk W).βY 0)

set_option maxHeartbeats 1000000 in

def StabAt (f : FamCh W u) (B : SBes W.S.X W.Q.instEq u W.Q.Rl.ψ (D.sp.X 0)) (a₀ a : GA D (D.sp.X 0)) : Prop :=
  ∀ κ : GA D (D.sp.Y 0), (κ ∈ GfC (D.sp.Y 0) ∧ finE (D.sp.Y 0) κ ∈ Formalism.L2.DIV.St (frAt f B a₀ a)) ↔
    ((iotaX W.S.X W.Q.instEq κ).1 = 1 ∧ (iotaX W.S.X W.Q.instEq κ).2 ∈ W.S.X.B.I.Kset)

end GlobalTheory.LevZero

end
