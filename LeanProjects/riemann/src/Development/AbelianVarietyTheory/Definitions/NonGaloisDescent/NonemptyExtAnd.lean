import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RatInEig
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnivChar
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.RealPoints
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CGTrue
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.CoreEq

noncomputable section

namespace GlobalTheory.TwInputs

open Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.Host Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.NX ReciprocityTheory.Gal
  NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.Col2 GlobalTheory.HeightCounting

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def RealSide.Framed {D : D7} (X : RealSide D) : Prop :=
  ∀ (j : Fin D.R.m) hV, GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.FramePin X.core X.R.toRealDat j X.core.σ₀ hV

theorem RealSide.space_eq {D : D7} (X : RealSide D) (j : Fin D.R.m) :
    X.core.V ((j : ℕ) + 1) X.core.σ₀ = Wc D j :=
  X.geo.fw.laws.spaceW _ ⟨Nat.le_add_left _ _, j.2⟩ _ X.core.toCore.good_σ₀

section At

variable (hL : GlobalTheory.Published.LocalLanglandsGL) (D : D7) (nch : NChoice D) (xd : ThData D) (first : Prop) {G : Type}
  [iG : Group G] [fG : Fintype G] {Pl0 I0 T : Type}
  {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {C : Formalism.L2.Pj.CoreJ D} [aC : Algebra C.Q.c.F D.what₂.LL]
  (R : RealDat3 D A3 C.Q.c.F) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd)
  (geo : GlobalTheory.RealGeo.GeoHalf C R.toRealDat fun _ => 1) (S : RatDat D.ntw) (YS : NExpRealS R cG S)

def TwAt (_H : NExpRealH R cG S YS) (cf : CharFrame D) : Type 1 :=
  TwJoin hL D nch xd first R F cG geo S YS cf

variable {hL D nch xd first R F cG geo S YS}

theorem TwAt.Sb_eq {H : NExpRealH R cG S YS} {cf : CharFrame D} (a : TwAt hL D nch xd first R F cG geo S YS H cf) :
    a.X.R.Sb = R.Sb := TwJoin.Sb_eq a

end At

def TwAt.ofBundles {hL : GlobalTheory.Published.LocalLanglandsGL} {D : D7} {nch : NChoice D} {xd : ThData D} {first : Prop}
    (X : RealSide D) (Y : SerSide X (twEOf xd)) (g : GalSide D) (h1 : g.cf = X.R.C) (h2 : g.lam.C = X.R.C) (hF : FieldOk X)
    (cg : CGTrue hL D g.wd) (hb : first → ∀ w, D.what₂.muAt w ≠ D.what₂.mu0 → BaseTup Y (nch.twI w))
    (H : NExpRealH X.R X.cG Y.S Y.YS) : TwAt hL D nch xd first X.R X.F X.cG X.geo Y.S Y.YS H X.R.C :=
  TwJoin.mk X rfl HEq.rfl HEq.rfl rfl rfl rfl rfl HEq.rfl HEq.rfl HEq.rfl HEq.rfl HEq.rfl HEq.rfl Y rfl HEq.rfl g h1 h2 rfl hF cg hb

def TwExt (hL : GlobalTheory.Published.LocalLanglandsGL) : NExt hL := fun _ B _ T w Z _ _ t nch _ xd c =>
  TwAt hL (w.st Z).toD7 nch xd (T = TwDat.untw B T.pl) t.r.z.R t.r.z.F t.r.z.cG t.r.z.geo _ c.row.nexp c.row.hecke (TC.cf w.I w.l Z)

def extAnd {hL : GlobalTheory.Published.LocalLanglandsGL} (E E' : NExt hL) : NExt hL := fun K B f T w Z Wt p0 t nch n xd c =>
  E K B f T w Z Wt p0 t nch n xd c × E' K B f T w Z Wt p0 t nch n xd c

section Rows

variable {hL : GlobalTheory.Published.LocalLanglandsGL} {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} {Z : w.Lt}
  {Wt : Set B.places.Pl} {p0 : BaseLevelRowSide (w.D Z)} {t : RowsT K w Z Wt p0} {nch : NChoice (w.D Z)} {n : NchT w Z Wt nch}
  {xd : ThData (w.D Z)}

def extAndNone (E : NExt hL) (c : NCore hL t n) :
    extAnd E (NExt.none hL) K B f T w Z Wt p0 t nch n xd c ≃ E K B f T w Z Wt p0 t nch n xd c := Equiv.prodPUnit _

def NXAnd.fst {E E' : NExt hL} (y : NX hL (extAnd E E') K B f T w Z Wt p0 t nch n xd) : NX hL E K B f T w Z Wt p0 t nch n xd :=
  ⟨y.1, y.2.1⟩

def NXAnd.snd {E E' : NExt hL} (y : NX hL (extAnd E E') K B f T w Z Wt p0 t nch n xd) : NX hL E' K B f T w Z Wt p0 t nch n xd :=
  ⟨y.1, y.2.2⟩

example {c : NCore hL t n} (a : TwExt hL K B f T w Z Wt p0 t nch n xd c) : a.X.R.Sb = t.r.z.R.Sb := TwAt.Sb_eq a

example {c : NCore hL t n} (a : TwExt hL K B f T w Z Wt p0 t nch n xd c) : a.X.R.C = TC.cf w.I w.l Z := a.C_eq

end Rows

end GlobalTheory.TwInputs

end
