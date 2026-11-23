import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RatInEig
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnivChar
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CGTrue

noncomputable section

namespace GlobalTheory.TwInputs

open Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.Host Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.NX ReciprocityTheory.Gal
  NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.Col2 GlobalTheory.HeightCounting

attribute [local instance] Formalism.BasicNotions.Host.cmStar

structure TwJoin (hL : GlobalTheory.Published.LocalLanglandsGL) (D : D7) (nch : NChoice D) (xd : ThData D) (first : Prop) {G : Type}
    [iG : Group G] [fG : Fintype G] {Pl0 I0 T : Type}
    {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {C : Formalism.L2.Pj.CoreJ D} [aC : Algebra C.Q.c.F D.what₂.LL]
    (R : RealDat3 D A3 C.Q.c.F) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd)
    (geo : GlobalTheory.RealGeo.GeoHalf C R.toRealDat fun _ => 1) (S : RatDat D.ntw) (YS : NExpRealS R cG S)
    (cf : CharFrame D) : Type 1 where
  X : RealSide D
  Γ_eq : X.Γ = G
  grp_eq : HEq X.grp iG
  fin_eq : HEq X.fin fG
  Pl0_eq : X.Pl0 = Pl0
  I0_eq : X.I0 = I0
  T_eq : X.T = T
  core_eq : X.core = C
  alg_eq : HEq X.alg aC
  R_eq : HEq X.R R
  F_eq : HEq X.F F
  cG_eq : HEq X.cG cG
  geo_eq : HEq X.geo geo
  A3_eq : HEq X.A3 A3
  Y : SerSide X (twEOf xd)
  S_eq : Y.S = S
  YS_eq : HEq Y.YS YS
  gal : GalSide D
  cf_eq : gal.cf = cf
  lam_eq : gal.lam.C = cf
  C_eq : X.R.C = cf
  field : FieldOk X
  cg : CGTrue hL D gal.wd
  base : first → ∀ w, D.what₂.muAt w ≠ D.what₂.mu0 → BaseTup Y (nch.twI w)

theorem TwJoin.Sb_eq {hL : GlobalTheory.Published.LocalLanglandsGL} {D : D7} {nch : NChoice D} {xd : ThData D} {first : Prop} {G : Type}
    [iG : Group G] [fG : Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {C : Formalism.L2.Pj.CoreJ D}
    [aC : Algebra C.Q.c.F D.what₂.LL] {R : RealDat3 D A3 C.Q.c.F} {F : Face3 D A3} {cG : G0 R.Pg D.R.r ≃* G0g D.nd}
    {geo : GlobalTheory.RealGeo.GeoHalf C R.toRealDat fun _ => 1} {S : RatDat D.ntw} {YS : NExpRealS R cG S}
    {cf : CharFrame D} (a : TwJoin hL D nch xd first R F cG geo S YS cf) : a.X.R.Sb = R.Sb := by
  obtain ⟨X, h1, h2, h3, h4, h5, h6, h7, h8, hR, -, -, -, hA, -⟩ := a
  cases X
  dsimp only at h1 h2 h3 h4 h5 h6 h7 h8 hR hA ⊢
  subst h1 h4 h5 h6 h7
  cases h2; cases h3; cases h8; cases hA; cases hR
  rfl

def TwOf (hL : GlobalTheory.Published.LocalLanglandsGL) : NExt hL := fun _ B _ T w Z _ _ t nch _ xd c =>
  TwJoin hL (w.st Z).toD7 nch xd (T = TwDat.untw B T.pl) t.r.z.R t.r.z.F t.r.z.cG t.r.z.geo _ c.row.nexp (TC.cf w.I w.l Z)

end GlobalTheory.TwInputs

end
