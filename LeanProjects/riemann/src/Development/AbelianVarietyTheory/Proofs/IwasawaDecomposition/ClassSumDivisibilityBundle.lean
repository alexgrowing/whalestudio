import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.GeometricWeakTiesOfStrong
import Development.AbelianVarietyTheory.Definitions.HeightFunctions.OntoAlong
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StrictHenselianAcyclic
import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.NonemptyAlgHomOfIsRayOfDvd
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ClassSumPin
import Development.AbelianVarietyTheory.Definitions.Divisors.RowSideOfCompatibleThetaPair
import Development.AbelianVarietyTheory.Definitions.Divisors.MapBaseTiedSel
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.IsLinked
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RootsOfUnityRingLeWittIntegers
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SubsetTwistExceptionalPlaces
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.TwArgs
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ClassSumOfPin

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.RT GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Fc
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.BigTop

namespace GlobalTheory.ClassSumPinLink

open Formalism.L2 Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.NX

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ}

set_option maxHeartbeats 2000000 in
set_option synthInstance.maxHeartbeats 400000 in

theorem classSumPin_of_read (p : PtAt ex Csz) (Yr : R3.Read (A3 := p.P.A3) p.R.toRealDat p.F.lv2 ex.p0)
    (hjW : ∀ (i : Fin D.R.m) (v : Fin ((p.P.A3.indefDown p.P.S0).dW i) → D.what₂.LL)
      (y : Fin (Module.finrank D.what₂.LL (p.R.toRealDat.WL p.F.lv2 false i)) → D.what₂.LL), HEq v y →
      Yr.mj.eW i (p.P.I.jW i v) = (p.R.FW i).j (sg0 D p.P.A3.A) (jDL p.R p.F.lv2 i y))
    (hth : GlobalTheory.HeightCounting.EMtTheta Yr p.nexp ex.nch)
    (hD : DivRows3 D p.P.A3 p.P.P0 p.P.ψ0 p.P.Ps p.P.ψs p.P.Zs p.P.S0 p.P.S1 ex.p0 p.P.C p.P.NuC p.P.I) :
    GlobalTheory.ExportPin.ClassSumPin p := by
  intro w i h1 h2 t ht hw c x hx hxT y hy n a f hsum
  subst hx
  apply hth w i hw _ hxT n a f
  rw [hsum, GlobalTheory.ExportPin.Model.theta_cast _ _ _ ht, hD.thTheta, hjW i _ y hy]

end GlobalTheory.ClassSumPinLink

namespace GlobalTheory.ClassSumPinLink

open Formalism.L2 Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.NX

section Pack

variable {D : D7} {O : Obj D}

set_option maxHeartbeats 2000000 in
set_option synthInstance.maxHeartbeats 400000 in

def ReadAt {R : Formalism.L2.RecT O.ex} {S : Formalism.L2.SG.SpectralTiesReal.STiesR R} (k : RPk R S) : Prop :=
  ∃ Yr : R3.Read (A3 := k.P.A3) k.B.Q.Rl.toRealDat
      (⟨k.P.P0, k.P.ψ0, k.P.Ps, k.P.ψs, k.Dc, k.Sp, k.Zsc⟩ : Face3 D k.P.A3).lv2 O.ex.p0,
    (∀ (i : Fin D.R.m) (v : Fin ((k.P.A3.indefDown k.P.S0).dW i) → D.what₂.LL)
      (y : Fin (Module.finrank D.what₂.LL (k.B.Q.Rl.toRealDat.WL
        (⟨k.P.P0, k.P.ψ0, k.P.Ps, k.P.ψs, k.Dc, k.Sp, k.Zsc⟩ : Face3 D k.P.A3).lv2 false i)) → D.what₂.LL),
      HEq v y → Yr.mj.eW i (k.P.I.jW i v) = (k.B.Q.Rl.FW i).j (sg0 D k.P.A3.A)
        (jDL k.B.Q.Rl (⟨k.P.P0, k.P.ψ0, k.P.Ps, k.P.ψs, k.Dc, k.Sp, k.Zsc⟩ : Face3 D k.P.A3).lv2 i y)) ∧
    GlobalTheory.HeightCounting.EMtTheta Yr k.B.Q.nexp O.ex.nch

set_option maxHeartbeats 2000000 in
set_option synthInstance.maxHeartbeats 400000 in

theorem readAt_rpkX {R : Formalism.L2.RecT O.ex} {S : Formalism.L2.SG.SpectralTiesReal.STiesR R} {x : R3.TwIn O.ex} (y : R3.RealIn x R S)
    (h : GlobalTheory.HeightCounting.EMtTheta x.Y y.nexp O.ex.nch) : ReadAt (rpkX y) := by
  refine ⟨x.Y, ?_, h⟩
  intro i v z hvz
  obtain rfl := eq_of_heq hvz
  exact x.Z.jW_read i v

set_option maxHeartbeats 4000000 in
set_option synthInstance.maxHeartbeats 400000 in

theorem classSumPin_of_readAt {c : ℝ} (b : Bundle D O c) (t : b.Comparison₂) (h : ReadAt (rpkB b)) (hD : Ind.PDiv D O c (b.part t)) :
    GlobalTheory.ExportPin.ClassSumPin (b.part t).pt := by
  obtain ⟨Yr, h1, h2⟩ := h
  exact classSumPin_of_read (b.part t).pt Yr h1 h2 hD

end Pack

end GlobalTheory.ClassSumPinLink

namespace GlobalTheory.ClassSumPinLink

open Formalism.L2 Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.NX

set_option maxHeartbeats 2000000 in
set_option synthInstance.maxHeartbeats 400000 in

theorem eMtTheta_of_pack {D : D7} {nch : NChoice D} {X0 : BaseLevelRowSide D} {G G' : Type} {g : Group G} {g' : Group G'} {fi : Fintype G}
    {fi' : Fintype G'} {Pl0 I0 T Pl0' I0' T' : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m}
    {A3' : FamIn3 D.what₂.LL G' Pl0' I0' (List ℕ) T' D.R.m}
    {C C' : CoreJ D} {al : Algebra C.Q.c.F D.what₂.LL} {al' : Algebra C'.Q.c.F D.what₂.LL} {R : RealDat3 D A3 C.Q.c.F}
    {R' : RealDat3 D A3' C'.Q.c.F} {F : Face3 D A3} {F' : Face3 D A3'} {kap : ℝ} {lam : type_of% R'.lam3} {err : type_of% R'.err0}
    {Dc : ∀ Zs : DefSub A3'.fam3.amb3, DefCols (A3'.side3 F'.P1 F'.ψ1 Zs)} {Sp : ∀ Zs, SPer (Dc Zs)}
    {Zsc : DefSub A3'.fam3.amb3 → IndefScale A3'.fam3.base3}
    {cG : G0 R.Pg D.R.r ≃* G0g D.nd} {cG' : G0 R'.Pg D.R.r ≃* G0g D.nd}
    {cG'' : G0 ((R'.updS kap lam).withErr err).Pg D.R.r ≃* G0g D.nd}
    (pack : (⟨G, g, fi, Pl0, I0, T, A3, C, al, R, F, cG⟩ :
      Σ' (G : Type) (_ : Group G) (_ : Fintype G) (Pl0 I0 T0 : Type)
        (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T0 D.R.m) (C : CoreJ D)
        (_ : Algebra C.Q.c.F D.what₂.LL) (R : RealDat3 D A3 C.Q.c.F) (_ : Face3 D A3),
        G0 R.Pg D.R.r ≃* G0g D.nd) =
      ⟨G', g', fi', Pl0', I0', T', A3', C', al', (R'.updS kap lam).withErr err, R3.reFace F' Dc Sp Zsc, cG''⟩)
    (Y : R3.Read (A3 := A3) R.toRealDat F.lv2 X0) (Y' : R3.Read (A3 := A3') R'.toRealDat F'.lv2 X0)
    (hW : HEq Y.mj.eW Y'.mj.eW) {S S' : RatDat D.ntw} (hS : S = S')
    (E : NExpRealS R cG S) (E' : NExpRealS R' cG' S') (hF : HEq E.eF E'.eF) (hi : HEq E.fi E'.fi)
    (h : GlobalTheory.HeightCounting.EMtTheta Y' E' nch) : GlobalTheory.HeightCounting.EMtTheta Y E nch := by
  cases pack
  cases hS
  intro w i hw x hx n a f hs
  have e1 : E.eF = E'.eF := eq_of_heq hF
  have e2 : E.fi = E'.fi := eq_of_heq hi
  have e3 : Y.mj.eW = Y'.mj.eW := eq_of_heq hW
  rw [e2, e3] at hs
  rw [e1]
  exact h w i hw x hx n a f hs

set_option maxHeartbeats 2000000 in
set_option synthInstance.maxHeartbeats 400000 in

theorem eMtTheta_of_args {hL : GlobalTheory.Published.LocalLanglandsGL} {K : Ctx} {B : GlobalTheory.Mem.Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T}
    {Z : w.Lt} {Wt : Set B.places.Pl} {L : SizeData₂ (w.st Z).toD7} {hT : GatTies (w.st Z).toD7} {Gi : Formalism.MainNotions.G.Inst (w.st Z).toD7 L}
    {Gl : Formalism.MainNotions.G.LatInst (w.st Z).toD7} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (w.st Z).toD7} {cX : ExtraC}
    {ex : Extra (w.st Z).toD7 L hT Gi Gl Kc Yd cX} (t : RowsT K w Z Wt ex.p0) (n : NchT w Z Wt ex.nch) (c : NCore hL t n)
    (a : R3.TwArgs ex t) (x : R3.TwIn ex) (ax : HEq a.x x) {Sx : RatDat (w.st Z).toD7.ntw} (E : NExpRealS x.R x.cG Sx)
    (hS : HEq Sx (ratDatR (D := (w.st Z).toD7) t.r.z.R t.r.z.cG c.row.kKs c.row.hk))
    (hF : HEq E.eF c.row.nexp.eF) (hi : HEq E.fi c.row.nexp.fi)
    (h : GlobalTheory.HeightCounting.EMtTheta (D := (w.st Z).toD7) t.r.Y c.row.nexp ex.nch) : GlobalTheory.HeightCounting.EMtTheta x.Y E ex.nch := by
  cases ax
  exact eMtTheta_of_pack a.pack a.x.Y t.r.Y a.eW (eq_of_heq hS) E c.row.nexp hF hi h

end GlobalTheory.ClassSumPinLink

namespace GlobalTheory.ClassSumPinLink

set_option maxHeartbeats 4000000 in

theorem pIota_classSumPin : ∀ (hL : GlobalTheory.Published.LocalLanglandsGL) (N : NExt hL) (S : SExt) (Γ : GeoP), (∀ K B f T w Z Wt p0 t nch n xd c, N K B f T w Z Wt p0 t nch n xd c → Nonempty (GlobalTheory.HeightCounting.Up.NEb hL K B f T w Z Wt p0 t nch n xd c)) → ∀ (K : Ctx) (q : WPt (prmR N S Γ).s K) (c : ℝ) (b : Bundle (q.w.D q.Z) q.O c) (_ : BWit (p := prmR N S Γ) q b) (t : b.Comparison₂), Ind.PIota _ _ c (b.part t) ∧ (Ind.PDiv _ _ c (b.part t) → GlobalTheory.ExportPin.ClassSumPin (b.part t).pt) := by
  intro hL N S Γ hN K q c b hb t
  refine ⟨?_, fun hD => ?_⟩
  · obtain ⟨sP, sS, -, -, hS⟩ := hb.s
    have key : ∀ S' : Formalism.L2.SG.SpectralTiesReal.STiesR b.R, S' = sS.toSTiesR b.R → ∀ x : S'.X.B.I.E, HEq (S'.X.ιE x) x := by
      rintro S' rfl
      exact sP.pin
    exact key b.S hS
  · have hth : GlobalTheory.HeightCounting.EMtTheta hb.x.Y hb.y.y.nexp q.O.ex.nch := by
      obtain ⟨m⟩ := hN _ _ _ _ _ _ _ _ _ _ _ _ _ q.x.nx.2
      exact eMtTheta_of_args q.x.what₂ q.x.n (WPt.core (p := prmR N S Γ) q) hb.a hb.x hb.ax hb.y.y.nexp hb.sx hb.eF hb.fi m.1.th
    have hR : ReadAt (rpkB b) := by
      rw [hb.y.eq]
      exact readAt_rpkX hb.y.y hth
    exact classSumPin_of_readAt b t hR hD

end GlobalTheory.ClassSumPinLink
