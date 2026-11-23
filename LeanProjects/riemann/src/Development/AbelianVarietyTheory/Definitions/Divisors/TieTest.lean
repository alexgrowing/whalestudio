import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SlopeTestRemainingChoicesAlt

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain
open Formalism.L2 Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest

namespace GlobalTheory.BigTop.Fun

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ}

def eV0 (p : PtAt ex Csz) (t : Tup p) : (Fin ((Df p).nV t) → D.what₂.LL) →ₗ[D.what₂.LL] p.P.A3.A.fam.amb.FR t :=
  ((p.P.A3.A.fam.R t).S.basis.equivFun.symm :
      (Fin (p.P.A3.A.fam.R t).S.dim → D.what₂.LL) →ₗ[D.what₂.LL] (p.P.A3.A.fam.R t).S.Forms) ∘ₗ
    ((p.P.A3.A.fam.R t).vE (p.P.A3.A.fam.lvl p.P.P0 p.P.ψ0)).mulVecLin

def InUse (p : PtAt ex Csz) (t : Tup p) : Prop := t = p.P.A3.A.μ0 ∨ ∃ w, p.R.mu w = t

variable {p : PtAt ex Csz} {CF : ℝ} (d : FunIn p CF) (a : SlopeTestRemainingChoices p d.G d.W d.n)

def TieTest : Prop := IsTestLat d.G a.rp d.n a.e d.X' d.M

def TieV : Prop := ∀ t, InUse p t → ∀ (x : Fin ((Df p).nV t) → D.what₂.LL) (i : Fin d.n),
  D.what₂.embLL ((d.V t).mulVec x i) = vK a.ch t (eV0 p t x) i

def TieSq : Prop :=
  IsSqOf d.W a.S.B a.rm CF p.P.A3.A.μ0 p.R.mu d.rq d.zA d.zA' d.zT d.zTd d.gT d.ch d.N0 d.Sd d.Se d.dl d.Bw

structure TieAt : Prop where

  ok : a.OK

  test : TieTest d a

  sums : TieV d a

  sq : TieSq d a

def Comparison₂ : TieT := fun p _ d => ∃ a : SlopeTestRemainingChoices p d.G d.W d.n, TieAt d a

end GlobalTheory.BigTop.Fun

end
