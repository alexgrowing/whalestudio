import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BesselLocalTypeData
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RealPack
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TrueW
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TopReadAt
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.STiesR
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.IndefRRealT
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.PlacedBy
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.InverseLevelCardinality
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ComIs
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.UnderMemS

set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam GlobalTheory.Core.Mi ValuativeRel
open Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowDict Formalism.L2.SG.PoincareInHH.PoincareSetting
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
namespace GlobalTheory.LevZero
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX}
theorem pg_isTypePlaces_alt (W : _root_.GlobalTheory.MiS.RealPackAlt ex) : GlobalTheory.Core.Mi.IsTypePlaces (_root_.GlobalTheory.Fam.pk_z W).Pg := by
  have H := W.Q.charW.base.lev
  let M := (_root_.GlobalTheory.Fam.pk_z W).toLevCh
  let μ := W.P.A3.A.μ0
  let M' : LevCh D Unit := { M with xiH := fun _ => M.xiH μ, xi := fun _ => M.xi μ, Q := fun _ => M.Q μ, xiR := fun _ => M.xiR μ }
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19⟩ := H
  exact GlobalTheory.SeeSaw.ComCols.isTypePlaces_of_levCh (L := M') ⟨h1, h2, fun _ => h3 _, fun _ _ _ => rfl, h5, fun _ => h6 _, fun _ => h7 _,
    fun _ => h8 _, h9, fun _ => h10 _, fun _ => h11 _, fun p hp => (h12 p hp).imp fun _ e _ => e _, fun _ => h13 _, h14, fun _ => h15 _,
    h16, h17, h18, h19⟩
set_option maxHeartbeats 1000000 in
theorem stZero_is_com_zero_of_pkHyp (W : _root_.GlobalTheory.MiS.RealPackAlt ex) (hP : _root_.GlobalTheory.Fam.PackageHypotheses W) (hm : 0 < D.R.m) : (_root_.GlobalTheory.LevZero.levelZeroState W).st.Is (_root_.GlobalTheory.BaseChain.com_z W) 0 := by
  have h := _root_.GlobalTheory.BaseChain.stage_y_is W hP 0 hm
  exact ⟨h.rank, h.sigOK, h.sig, h.par, h.selfDual, h.frame, h.base, ⟨r_le_Y 0, fun _ => 1, rfl⟩, h.haar, h.fund⟩
set_option maxHeartbeats 1000000 in
theorem bot_stZero_of_gRead (W : _root_.GlobalTheory.MiS.RealPackAlt ex) (hP : _root_.GlobalTheory.Fam.PackageHypotheses W) (hm : 0 < D.R.m) {u : D.what₂.Word} (f : _root_.GlobalTheory.Fam.FamilyCharacter W u) (v : VCom f.c) (hv : v.Is)
    (ht : _root_.GlobalTheory.Fam.CommutingVectorTie f v) {n : ℕ} (G : (_root_.GlobalTheory.Fam.pk_z W).Pg → GLoc v) (pl : Fin n ≃ (_root_.GlobalTheory.Fam.pk_z W).Pg) (hR : _root_.GlobalTheory.Fam.LocalGroupReading f (fun i => G (pl i)) pl) :
    Bot (c := f.c) (_root_.GlobalTheory.BaseChain.com_z W) (_root_.GlobalTheory.LevZero.levelZeroState W) (f.g.b 0) G := by
  refine ⟨_root_.GlobalTheory.BaseChain.com_is_alt W hP, rfl, _root_.GlobalTheory.LevZero.stZero_is_com_zero_of_pkHyp W hP hm, ?_, _root_.GlobalTheory.LevZero.pg_isTypePlaces_alt W, ?_, ?_, ?_⟩
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
theorem bot_of_placedBy_alt : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.PackageHypotheses W → ∀ (u : D.what₂.Word) (f : _root_.GlobalTheory.Fam.FamilyCharacter W u) (B : SBes W.S.X W.Q.instEq u W.Q.Rl.ψ (D.sp.X 0)), ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : Type) (v : VCom f.c) (o : TDat f.c k ι) (n : ℕ) (G : Fin n → GLoc v) (pl : Fin n ≃ (_root_.GlobalTheory.Fam.pk_z W).Pg), _root_.GlobalTheory.LevZero.PlacedByLocalGroups f B v o G pl → GlobalTheory.LevZero.Bot (c := f.c) (_root_.GlobalTheory.BaseChain.com_z W) (_root_.GlobalTheory.LevZero.levelZeroState W) (f.g.b 0) (fun PP => G (pl.symm PP)) := by
  intro D L hT Gi Gl Kc Yd cX ex W hP u f B k _ _ _ _ ι v o n G pl h
  have hm : 0 < D.R.m := by have := D.R.two_le_m; omega
  have e : (fun i => G (pl.symm (pl i))) = G := funext fun i => by rw [Equiv.symm_apply_apply]
  have hR : _root_.GlobalTheory.Fam.LocalGroupReading f (fun i => G (pl.symm (pl i))) pl := by rw [e]; exact h.read
  exact _root_.GlobalTheory.LevZero.bot_stZero_of_gRead W hP hm f v h.vis h.tie (fun PP => G (pl.symm PP)) pl hR
end GlobalTheory.LevZero
end
end
