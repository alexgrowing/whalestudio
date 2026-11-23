import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.GKeyFin
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.GoodPairSystems
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RowRatW
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.GoodReductionCondition
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Statements.CuspidalUnitaryTwists.ExistsSmallSpherical
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PositionMv
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RowTestSetting
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LeastSplitAuxiliaryPrimeLtScaleBound
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WeightOnePlacesAreTwistPlacesOfWitness
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BwitFrameTwists
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RowEListPinPt
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Fc GlobalTheory.RowEx GlobalTheory.Mem.LiteralAutomorphy
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.LiteralAutomorphy.GridRow

theorem eventually_sizeRows_and_logDeriv_le (hL : GlobalTheory.Published.LocalLanglandsGL) (p : Prm hL) : EvP fun _ K => ∀ β : BPt K, β.Is (IsGoodE p.s) →
    GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup.SizeRows β.O.L ∧ |β.O.L.logDerivativeAtOne| ≤ K.s.x ^ K.s.eps := by
  refine (GlobalTheory.Mem.AtSize.eventually_sizeRows hL p).mono fun κ K _ H β hq => ⟨H β hq, ?_⟩
  have h := β.val.dlog
  rw [β.sc] at h
  exact h

set_option maxHeartbeats 1000000 in

theorem rowE_full_grid (hL : GlobalTheory.Published.LocalLanglandsGL) (CF : ℝ) (N : NExt hL) (S : SExt) (Γ : GeoP) : RowE (IsGoodE (prmR (NEa hL N (GridA CF)) S Γ).s) (IsLinked (prmR (NEa hL N (GridA CF)) S Γ)) fun _ D O c b => ∀ t : b.Comparison₂, (b.part t).pt.Ties → ∀ G₀ : GlobalTheory.BigTop.Fun.Grid (b.part t).pt CF, ∃ G : GlobalTheory.BigTop.Fun.Grid (b.part t).pt CF, G.pl.v0 = G₀.pl.v0 ∧ G.pl.w G.pl.v0 = G₀.pl.w G₀.pl.v0 ∧ (∀ a : Fin D.R.m, G.ch.chiH (a.1 + 1) = G₀.ch.chiH (a.1 + 1)) ∧ Full (b.part t).pt.R.toRealDat G := by
  refine (eventually_sizeRows_and_logDeriv_le hL (prmR (NEa hL N (GridA CF)) S Γ)).mono fun κ K hk H β hq c b hl => ?_
  obtain ⟨q, b', ⟨w⟩, he⟩ := hl
  have h2 : (⟨β.D, β.O⟩ : Σ D : D7, Obj D) = ⟨q.w.D q.Z, q.O⟩ :=
    congrArg (fun s : Σ (D : D7) (O : Obj D), GlobalTheory.Fc.Bundle D O c => (⟨s.1, s.2.1⟩ : Σ D : D7, Obj D)) he
  have hL' : GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup.SizeRows q.O.L ∧ |q.O.L.logDerivativeAtOne| ≤ K.s.x ^ K.s.eps :=
    Eq.ndrec (motive := fun s : Σ D : D7, Obj D => GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup.SizeRows s.2.L ∧ |s.2.L.logDerivativeAtOne| ≤ K.s.x ^ K.s.eps) (H β hq) h2
  have hsc0 : β.O.L.sc = K.s := β.sc
  have hsc : q.O.L.sc = K.s := Eq.ndrec (motive := fun s : Σ D : D7, Obj D => s.2.L.sc = K.s) hsc0 h2
  have hA : GridA CF K q.B q.f q.T := q.x.nx.2.2.down
  have hG : GridAt K.s CF (q.w.st q.Z) q.f (q.T.set q.f) := hA _ _ _ _ _ _
  suffices key : ∀ t : b'.Comparison₂, (b'.part t).pt.Ties → ∀ G₀ : GlobalTheory.BigTop.Fun.Grid (b'.part t).pt CF,
      ∃ G : GlobalTheory.BigTop.Fun.Grid (b'.part t).pt CF, G.pl.v0 = G₀.pl.v0 ∧ G.pl.w G.pl.v0 = G₀.pl.w G₀.pl.v0 ∧
        (∀ a : Fin (q.w.D q.Z).R.m, G.ch.chiH (a.1 + 1) = G₀.ch.chiH (a.1 + 1)) ∧ Full (b'.part t).pt.R.toRealDat G by
    have h1 := congrArg (fun s : Σ (D : D7) (O : Obj D), GlobalTheory.Fc.Bundle D O c => ∀ t : s.2.2.Comparison₂, (s.2.2.part t).pt.Ties →
      ∀ G₀ : GlobalTheory.BigTop.Fun.Grid (s.2.2.part t).pt CF, ∃ G : GlobalTheory.BigTop.Fun.Grid (s.2.2.part t).pt CF, G.pl.v0 = G₀.pl.v0 ∧
        G.pl.w G.pl.v0 = G₀.pl.w G₀.pl.v0 ∧ (∀ a : Fin s.1.R.m, G.ch.chiH (a.1 + 1) = G₀.ch.chiH (a.1 + 1)) ∧
        Full (s.2.2.part t).pt.R.toRealDat G) he
    exact cast h1.symm key
  intro t ht G₀
  obtain ⟨hW1, hEx, hfin⟩ := GlobalTheory.Mem.Top.Bl.weight_one_places_are_twist_places_of_witness hL _ K q c b' w hsc
  obtain ⟨hC, hoff, hxi⟩ := GlobalTheory.RowEx.bwit_frame_twists hL _ K q c b' w
  have hset : GlobalTheory.RowClaim.HidaSetting q.O.L b'.B.Q.Rl.toRealDat b'.B.Q.F.lv2 :=
    GlobalTheory.PrimIn.rowTest_setting _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ b'.B t.pins hW1 hEx hL'.1 ht.eSer hfin
  have hrec : GlobalTheory.SqTop.Rec q.O.L := ⟨hL'.1, hset.host, hset.hF, by rw [hsc]; exact hL'.2⟩
  have hb : (b'.part t).pt.Z.b = K.s.b := by
    have h0 : (b'.part t).pt.Z.b = q.O.L.sc.b := rfl
    rw [h0, hsc]
  have gen : ∀ z : ℝ, z = K.s.b → ∀ G₀ : GlobalTheory.ChiGrid.GridData b'.B.Q.Rl.toRealDat.toLevCh ⟨1, CF, z⟩,
      ∃ G : GlobalTheory.ChiGrid.GridData b'.B.Q.Rl.toRealDat.toLevCh ⟨1, CF, z⟩, G.pl.v0 = G₀.pl.v0 ∧ G.pl.w G.pl.v0 = G₀.pl.w G₀.pl.v0 ∧
        (∀ a : Fin (q.w.D q.Z).R.m, G.ch.chiH (a.1 + 1) = G₀.ch.chiH (a.1 + 1)) ∧ Full b'.B.Q.Rl.toRealDat G := by
    rintro z rfl G₀
    obtain ⟨G, hk, hF⟩ := @hG q.O.L hsc hrec _ _ _ _ _ _ _ _ _ b'.B.alg b'.B.Q.Rl.toRealDat b'.B.Q.F.lv2 hset hC hoff hxi G₀
    exact ⟨G, congrArg Prod.fst hk, congrArg (fun x => x.2.1) hk, fun a => congrFun (congrArg (fun x => x.2.2) hk) a, hF⟩
  exact gen _ hb G₀

set_option maxHeartbeats 4000000 in

theorem rowE_pinned_grid (hL : GlobalTheory.Published.LocalLanglandsGL) (CF : ℝ) (N : NExt hL) (S : SExt) (Γ : GeoP) (hN : ∀ K B f T w Z Wt p0 t nch n xd c, N K B f T w Z Wt p0 t nch n xd c → Nonempty (GlobalTheory.HeightCounting.Up.NEl hL CF K B f T w Z Wt p0 t nch n xd c)) : RowE (IsGoodE (prmR (NEa hL N (GridA CF)) S Γ).s) (IsLinked (prmR (NEa hL N (GridA CF)) S Γ)) fun _ D O c b => ∀ t : b.Comparison₂, (b.part t).pt.Ties → ∃ G₀ : GlobalTheory.BigTop.Fun.Grid (b.part t).pt CF, GlobalTheory.BigTop.Fun.FieldHas G₀ (Formalism.L2.Host.embLL0 D) ∧ GlobalTheory.LamTie.IsLamTieFull D.ntw (GlobalTheory.BigTop.Fun.lamOf G₀) := by
  refine RowE.of_all fun κ K β c b _ _ hl => ?_
  obtain ⟨q, b', ⟨w⟩, he⟩ := hl
  have hsc : β.O.L.sc = K.s := β.sc
  have hsc' : q.O.L.sc = K.s := by
    have := congrArg (fun s : Σ (D : D7) (O : Obj D), Bundle D O c => s.2.1.L.sc) he
    exact this.symm.trans hsc
  have e := congrArg (fun s : Σ (D : D7) (O : Obj D), Bundle D O c => ∀ t : s.2.2.Comparison₂, (s.2.2.part t).pt.Ties →
    ∃ G₀ : GlobalTheory.BigTop.Fun.Grid (s.2.2.part t).pt CF, GlobalTheory.BigTop.Fun.FieldHas G₀ (Formalism.L2.Host.embLL0 s.1) ∧
      GlobalTheory.LamTie.IsLamTieFull s.1.ntw (GlobalTheory.BigTop.Fun.lamOf G₀)) he
  refine cast e.symm ?_
  intro t _
  obtain ⟨nl⟩ := hN _ _ _ _ _ _ _ _ _ _ _ _ _ q.x.nx.2.1
  have hp : GlobalTheory.HeightCounting.Up.ListPin (q.w.st q.Z).toD7 q.x.what₂.r.z.R.toRealDat.toLevCh CF K.s.b := nl.2.down
  have h1 := GlobalTheory.Mem.LiteralAutomorphy.PinPt.listPin_twArgs w.a hp
  rw [eq_of_heq w.ax] at h1
  have h2 := GlobalTheory.Mem.LiteralAutomorphy.PinPt.listPin_rpk w.y.y (rpkB b') w.y.eq h1
  rw [← hsc'] at h2
  exact h2

end GlobalTheory.Mem.LiteralAutomorphy.GridRow

end
