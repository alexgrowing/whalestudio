import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.CxTiesOf

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mi

namespace GlobalTheory.MiS.Check

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX}

theorem used_base (P : RowSideFamily ex) : Formalism.IndefR.RecTie.Used0 D (P.I.tup P.A3.A.μ0) := Or.inl P.tied.div.tup.mu0

theorem mu_eq_of_heq (P : RowSideFamily ex) {Zs : DefSub P.A3.fam3.amb3} (h : Zs = P.Zs)
    (S : IndefData (P.A3.side3 P.P0 P.ψ0 Zs)) (hS : HEq S P.S0) : S.μ = P.S0.μ := by
  subst h
  rw [eq_of_heq hS]

theorem used_all (W : RealPack ex) (t : W.P.T) : Formalism.IndefR.RecTie.Used0 D (W.P.I.tup t) := by
  rcases W.Q.charW.tup.mu_used t with h | ⟨w, h⟩
  · rw [h]; exact used_base W.P
  · right
    have e : W.Q.Rl.mu = W.P.S0.μ := mu_eq_of_heq W.P W.Q.zs _ W.Q.s0
    refine ⟨D.plEq.symm w, ?_⟩
    rw [W.P.tied.div.tup.muAt, Equiv.apply_symm_apply, ← h, e]
    rfl

theorem dcPtG_iff (W : RealPack ex) : DcPtG W.P ↔ RowsHoldDcPt3 W.P :=
  ⟨fun h u t x F => h u t (used_all W t) x F, fun h u t _ x F => h u t x F⟩

theorem hypAt_iff (W : RealPack ex) : HypAt W ↔
    Nonempty (Formalism.L2.SG.JoinSI.JoinSI W.R W.S W.Q) ∧ RowsHoldDcPt3 W.P ∧ W.Q.Rl.Char3 W.Q.F ∧ FramesOKg2 W.Q.Rl :=
  ⟨fun h => ⟨h.1, (dcPtG_iff W).1 h.2.2.1, h.2.2.2⟩, fun h => ⟨h.1, W.S.lev, (dcPtG_iff W).2 h.2.1, h.2.2⟩⟩

theorem hypAt_of (W : RealPack ex) (hJ : Nonempty (Formalism.L2.SG.JoinSI.JoinSI W.R W.S W.Q)) (hP : RowsHoldDcPt3 W.P)
    (hE : W.Q.Rl.toRealDat.ExAt) (hF : W.Q.FramesEx) : HypAt W :=
  (hypAt_iff W).2 ⟨hJ, hP, RealDat3.characterisation_of_weak W.Q.charW hE, W.Q.frames hF⟩

theorem period_rational {P : RowSideFamily ex} (h : DcPtG P) (u : D.what₂.Word) (x : Fin (P.Dc.a (P.I.wU u)) → D.what₂.LL)
    (F : Fin ((P.A3.side3 P.Ps P.ψs P.Zs).nV P.A3.A.μ0) → D.what₂.LL) :
    D.what₂.perCol u (P.I.tup P.A3.A.μ0) (D.jN u (P.I.eNu u x))
      (P.I.jA P.A3.A.μ0 ((rV0 D P.A3.A P.Ps P.ψs P.A3.A.μ0).mulVec F)) ∈ Set.range D.what₂.embLL :=
  ⟨_, h u _ (used_base P) x F⟩

theorem cornerCoordinate_automatic (W : RealPack ex) : (cxW W).CoordinatesInGoodPart W.Q.F.cr W.Q.F.cv true :=
  Formalism.IndefR.Cx.definite_coordinates_in_good_part _ true

theorem tiesRest_of_cxTies (W : RealPack ex)
    (h : CxTies (cxW W) W.Q.F.cr W.Q.F.cv (W.Q.F.eV (cxW W).zs)) : TiesRest W :=
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.2.2.2.2.1⟩

end GlobalTheory.MiS.Check

end
