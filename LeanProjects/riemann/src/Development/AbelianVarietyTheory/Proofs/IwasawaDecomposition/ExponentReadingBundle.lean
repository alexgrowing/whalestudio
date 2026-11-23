import Mathlib
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.GeometricWeakTiesOfStrong
import Development.AbelianVarietyTheory.Definitions.HeightFunctions.OntoAlong
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StrictHenselianAcyclic
import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.NonemptyAlgHomOfIsRayOfDvd
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.IsLinked
import Development.AbelianVarietyTheory.Definitions.Divisors.MapBaseTiedSel
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.RT GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Fc
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.PlugPt

open GlobalTheory.Mem.R3 Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links

set_option maxHeartbeats 4000000 in

theorem sidePt_part_of_pack {D : D7} {O : Obj D} {c : ℝ} (b : Bundle D O c) (t : b.Comparison₂) {x : R3.TwIn O.ex}
    (y : R3.RealIn x b.R b.S) (h : rpkB b = rpkX y) :
    ∃ Tp : Formalism.L2.Host.TupTied D x.R.C O.ex.nch, HEq Tp t.1.Tp ∧
      sidePt (O := O) (b.part t).pt = ({ G := x.G, Pl0 := x.Pl0, I0 := x.I0, T := x.T, A3 := x.A3, J := x.core, R := x.R, P0 := x.F.P0, ψ0 := x.F.ψ0, cG := x.cG, v₀ := x.geo.v₀, S := y.Sx, YS := y.nexp, cf := x.R.C, tp := Tp } : Side D O.ex.nch) := by
  have key : ∀ (p : RPk b.R b.S) (_ : p = rpkX y) (Tq : Formalism.L2.Host.TupTied D p.B.Q.Rl.C O.ex.nch),
      ∃ Tp : Formalism.L2.Host.TupTied D x.R.C O.ex.nch, HEq Tp Tq ∧
        ({ G := p.P.Gp, Pl0 := p.P.Pl0, I0 := p.P.I0, T := p.P.T, A3 := p.P.A3, J := p.B.T, alg := p.B.alg, R := p.B.Q.Rl, P0 := p.P.P0, ψ0 := p.P.ψ0, cG := p.B.Q.cG, v₀ := p.B.v₀, S := p.B.Q.Sx, YS := p.B.Q.nexp, cf := p.B.Q.Rl.C, tp := Tq } : Side D O.ex.nch) =
          ({ G := x.G, Pl0 := x.Pl0, I0 := x.I0, T := x.T, A3 := x.A3, J := x.core, R := x.R, P0 := x.F.P0, ψ0 := x.F.ψ0, cG := x.cG, v₀ := x.geo.v₀, S := y.Sx, YS := y.nexp, cf := x.R.C, tp := Tp } : Side D O.ex.nch) := by
    intro p hp Tq
    subst hp
    exact ⟨Tq, HEq.rfl, rfl⟩
  exact key (rpkB b) h t.1.Tp

set_option maxHeartbeats 4000000 in

theorem side_mk_eq_upd {D : D7} {nch : NChoice D} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type}
    {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {J : Formalism.L2.Pj.CoreJ D} [Algebra J.Q.c.F D.what₂.LL] (R : RealDat3 D A3 J.Q.c.F)
    (kap : ℝ) (lam : type_of% R.lam3) (err : type_of% R.err0) (P0 P0' : Subgroup G) (ψ0 : P0 →* D.what₂.LLˣ) (ψ0' : P0' →* D.what₂.LLˣ)
    (cG : G0 R.Pg D.R.r ≃* G0g D.nd) (v v' : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.toRealDat.MW i σ).Vec)
    (S S' : Formalism.IndefR.NX.RatDat D.ntw) (Y : Formalism.IndefR.NX.NExpRealS ((R.updS kap lam).withErr err) cG S)
    (Y' : Formalism.IndefR.NX.NExpRealS R cG S') (cf : Formalism.L2.Host.CharFrame D) (tp : Formalism.L2.Host.TupTied D R.C nch)
    (tp' : Formalism.L2.Host.TupTied D cf nch) (hP : P0 = P0') (hψ : HEq ψ0 ψ0') (hv : HEq v v') (hS : HEq S S') (hfi : HEq Y.fi Y'.fi)
    (heF : HEq Y.eF Y'.eF) (hcf : R.C = cf) (htp : HEq tp tp') :
    ({ G := G, Pl0 := Pl0, I0 := I0, T := T, A3 := A3, J := J, R := (R.updS kap lam).withErr err, P0 := P0, ψ0 := ψ0, cG := cG, v₀ := v, S := S, YS := Y, cf := R.C, tp := tp } : Side D nch) =
      Side.upd { G := G, Pl0 := Pl0, I0 := I0, T := T, A3 := A3, J := J, R := R, P0 := P0', ψ0 := ψ0', cG := cG, v₀ := v', S := S', YS := Y', cf := cf, tp := tp' } kap lam err := by
  subst hP hcf
  cases eq_of_heq hψ
  cases eq_of_heq hv
  cases eq_of_heq hS
  cases eq_of_heq htp
  obtain ⟨fi, _, _, _, eF, _, _⟩ := Y
  obtain ⟨fi', _, _, _, eF', _, _⟩ := Y'
  replace hfi : fi = fi' := (eq_of_heq hfi)
  replace heF : eF = eF' := (eq_of_heq heF)
  subst hfi heF
  rfl

set_option maxHeartbeats 4000000 in

theorem side_eq_upd {D : D7} {O : Obj D} (x : R3.TwIn O.ex) (s : Side D O.ex.nch) (kap : ℝ) (lam : type_of% s.R.lam3)
    (err : type_of% s.R.err0) (F : Face3 D s.A3) (Sx : Formalism.IndefR.NX.RatDat D.ntw) (YS : Formalism.IndefR.NX.NExpRealS x.R x.cG Sx)
    (Tp : Formalism.L2.Host.TupTied D x.R.C O.ex.nch)
    (pack : (⟨x.G, x.grp, x.fin, x.Pl0, x.I0, x.T, x.A3, x.core, x.alg, x.R, x.F, x.cG⟩ :
      Σ' (G : Type) (_ : Group G) (_ : Fintype G) (Pl0 I0 T0 : Type)
        (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T0 D.R.m) (C : Formalism.L2.Pj.CoreJ D)
        (_ : Algebra C.Q.c.F D.what₂.LL) (R : RealDat3 D A3 C.Q.c.F) (_ : Face3 D A3),
        G0 R.Pg D.R.r ≃* G0g D.nd) =
      ⟨s.G, s.grp, s.fin, s.Pl0, s.I0, s.T, s.A3, s.J, s.alg, (s.R.updS kap lam).withErr err, F, s.cG⟩)
    (hP : F.P0 = s.P0) (hψ : HEq F.ψ0 s.ψ0) (hv : HEq x.geo.v₀ s.v₀) (hS : HEq Sx s.S) (hfi : HEq YS.fi s.YS.fi)
    (heF : HEq YS.eF s.YS.eF) (hcf : s.R.C = s.cf) (htp : HEq Tp s.tp) :
    ({ G := x.G, Pl0 := x.Pl0, I0 := x.I0, T := x.T, A3 := x.A3, J := x.core, R := x.R, P0 := x.F.P0, ψ0 := x.F.ψ0, cG := x.cG, v₀ := x.geo.v₀, S := Sx, YS := YS, cf := x.R.C, tp := Tp } : Side D O.ex.nch) = s.upd kap lam err := by
  obtain ⟨G, Pl0, I0, T, A3, J, R, P0, ψ0, cG, v₀, S, Y, cf, tp⟩ := s
  obtain ⟨G', Pl0', I0', T', A3', core, R', F', cG', geo⟩ := x
  cases pack
  exact side_mk_eq_upd R kap lam err _ _ _ _ cG _ _ _ _ _ _ _ _ _ hP hψ hv hS hfi heF hcf htp

set_option maxHeartbeats 4000000 in

theorem pinPt_part_of_wit : ∀ (hL : GlobalTheory.Published.LocalLanglandsGL) (N : NExt hL) (S : SExt) (Γ : GeoP) (hE : GlobalTheory.PlugPt.HasExp N) (K : Ctx) (q : WPt (prmR N S Γ).s K) (c : ℝ) (b : Bundle (q.w.D q.Z) q.O c) (_ : BWit (p := prmR N S Γ) q b) (t : b.Comparison₂), GlobalTheory.PlugPt.pinPt (GlobalTheory.PlugPt.NRead.of RX hE (SXE S) (OX Γ)) K q c (b.part t).pt := by
  intro hL N S Γ hE K q c b w t
  obtain ⟨x, a, ax, y, recPin, -, -, sx, eF, fi, -⟩ := w
  obtain rfl := eq_of_heq ax
  obtain ⟨Tp, hTp, h⟩ := sidePt_part_of_pack b t y.y y.eq
  have htp : HEq Tp q.x.n.tp := hTp.trans (t.1.tpEq.trans (Sigma.mk.inj_iff.mp recPin.s.chr).2)
  have hcf : q.x.what₂.r.z.R.C = GlobalTheory.Mem.Col2.TC.cf q.w.I q.w.l q.Z := q.x.what₂.r.z.lev.C
  refine ⟨q.x.what₂.r.z.R.kap, a.lam, a.err, h.trans ?_⟩
  refine side_eq_upd (O := q.O) a.x (sideOf q.x.what₂ q.x.n q.core) q.x.what₂.r.z.R.kap a.lam a.err (reFace q.x.what₂.r.z.F a.Dc a.Sp a.Zsc :)
    y.y.Sx y.y.nexp Tp ?pack rfl HEq.rfl ?v ?S ?fi ?eF hcf htp
  case pack => exact (by with_unfolding_all exact (a.pack :))
  case v => exact (by with_unfolding_all exact (a.v₀ :))
  case S => exact (by with_unfolding_all exact (sx :))
  case fi => exact (by with_unfolding_all exact (fi :))
  case eF => exact (by with_unfolding_all exact (eF :))

end GlobalTheory.PlugPt
