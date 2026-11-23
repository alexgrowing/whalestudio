import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PlacedBy
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BaseChainCommutationValid
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BaseChainStageYValid
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsTypePlacesOfLevCh
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam GlobalTheory.Core.Mi ValuativeRel
open Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowDict Formalism.L2.SG.PoincareInHH.PoincareSetting
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.LevZero

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX}

theorem pg_isTypePlaces (W : RealPack ex) : GlobalTheory.Core.Mi.IsTypePlaces (pk W).Pg := by
  have H := W.Q.charW.base.lev
  let M := (pk W).toLevCh
  let μ := W.P.A3.A.μ0
  let M' : LevCh D Unit := { M with xiH := fun _ => M.xiH μ, xi := fun _ => M.xi μ, Q := fun _ => M.Q μ, xiR := fun _ => M.xiR μ }
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19⟩ := H
  exact GlobalTheory.SeeSaw.ComCols.isTypePlaces_of_levCh (L := M') ⟨h1, h2, fun _ => h3 _, fun _ _ _ => rfl, h5, fun _ => h6 _, fun _ => h7 _,
    fun _ => h8 _, h9, fun _ => h10 _, fun _ => h11 _, fun p hp => (h12 p hp).imp fun _ e _ => e _, fun _ => h13 _, h14, fun _ => h15 _,
    h16, h17, h18, h19⟩

set_option maxHeartbeats 1000000 in

theorem stZero_is (W : RealPack ex) (hP : PkHyp W) (hm : 0 < D.R.m) : (stZero W).st.Is (GlobalTheory.BaseChain.com W) 0 := by
  have h := GlobalTheory.BaseChain.stageY_is W hP 0 hm
  exact ⟨h.rank, h.sigOK, h.sig, h.par, h.selfDual, h.frame, h.base, ⟨r_le_Y 0, fun _ => 1, rfl⟩, h.haar, h.fund⟩

set_option maxHeartbeats 1000000 in

theorem bot_of_read (W : RealPack ex) (hP : PkHyp W) (hm : 0 < D.R.m) {u : D.what₂.Word} (f : FamCh W u) (v : VCom f.c) (hv : v.Is)
    (ht : VTie f v) {n : ℕ} (G : (pk W).Pg → GLoc v) (pl : Fin n ≃ (pk W).Pg) (hR : GRead f (fun i => G (pl i)) pl) :
    Bot (c := f.c) (GlobalTheory.BaseChain.com W) (stZero W) (f.g.b 0) G := by
  refine ⟨GlobalTheory.BaseChain.com_is W hP, rfl, stZero_is W hP hm, ?_, pg_isTypePlaces W, ?_, ?_, ?_⟩
  · have h := hv.b 0
    rw [ht.b 0] at h
    exact h
  · intro PP
    obtain ⟨i, rfl⟩ := pl.surjective PP
    exact ⟨(hR.idem i).1, (hR.idem i).2, fun a ha => hR.frame i 0 a ha⟩
  · intro g
    refine (hR.lev g).1.trans ⟨fun h PP => ?_, fun h i => h (pl i)⟩
    obtain ⟨i, rfl⟩ := pl.surjective PP
    exact h i
  · intro g x hx
    have h := (hR.lev g.1).2 g.2 (fun i => x (pl i)) (fun i => hx (pl i))
    exact h.trans (Equiv.prod_comp pl (fun PP => (G PP).S.P.lam (x PP)))

set_option maxHeartbeats 1000000 in

theorem bot_of_placedBy : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : RealPack ex), PkHyp W → ∀ (u : D.what₂.Word) (f : FamCh W u) (B : SBes W.S.X W.Q.instEq u W.Q.Rl.ψ (D.sp.X 0)), ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : Type) (v : VCom f.c) (o : TDat f.c k ι) (n : ℕ) (G : Fin n → GLoc v) (pl : Fin n ≃ (pk W).Pg), GlobalTheory.LevZero.PlacedBy f B v o G pl → GlobalTheory.LevZero.Bot (c := f.c) (GlobalTheory.BaseChain.com W) (GlobalTheory.LevZero.stZero W) (f.g.b 0) (fun PP => G (pl.symm PP)) := by
  intro D L hT Gi Gl Kc Yd cX ex W hP u f B k _ _ _ _ ι v o n G pl h
  have hm : 0 < D.R.m := by have := D.R.two_le_m; omega
  have e : (fun i => G (pl.symm (pl i))) = G := funext fun i => by rw [Equiv.symm_apply_apply]
  have hR : GRead f (fun i => G (pl.symm (pl i))) pl := by rw [e]; exact h.read
  exact bot_of_read W hP hm f v h.vis h.tie (fun PP => G (pl.symm PP)) pl hR

end GlobalTheory.LevZero

end
