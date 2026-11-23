import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.WeakCharInertPartRealAdelicDataTransport
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FinTypRepCast

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH NumberField IsDedekindDomain Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links
open Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Lev Formalism.L2.Pj Formalism.L2.Host
open Formalism.IndefR.RecTie Formalism.L2.Rows GlobalTheory.RealGeo
open scoped TensorProduct

namespace GlobalTheory.Mem.R3

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {B : Base} {C : Cols B}

structure Refill (a : Late B C) where

  S : SStage B C a.W

  G : GJStage B C

  L : ∀ u, Submodule (𝓞 B.LL) (a.V.div.Nu u).V

  h : B.Word → ℝ

  HH : ℝ

  HH_ge : sFrame (fun u => { a.V.div.Nu u with L := L u }) h + a.V.div.RR.muMax ≤ HH

  etaF : ℝ

abbrev Refill.to {a : Late B C} (c : Refill a) : Late B C :=
  ⟨a.W, { a.V with
      div := { a.V.div with Nu := fun u => { a.V.div.Nu u with L := c.L u }, h := c.h, HH := c.HH, HH_ge := c.HH_ge, etaF := c.etaF } },
    c.S, a.N, c.G⟩

abbrev Refill.ofSG (a : Late B C) (S : SStage B C a.W) (G : GJStage B C) : Refill a :=
  ⟨S, G, fun u => (a.V.div.Nu u).L, a.V.div.h, a.V.div.HH, a.V.div.HH_ge, a.V.div.etaF⟩

theorem Refill.ofSG_to (a : Late B C) (S : SStage B C a.W) (G : GJStage B C) : (Refill.ofSG a S G).to = ⟨a.W, a.V, S, a.N, G⟩ := rfl

abbrev Refill.ofDiv (a : Late B C) (L : ∀ u, Submodule (𝓞 B.LL) (a.V.div.Nu u).V) (h : B.Word → ℝ) : Refill a :=
  ⟨a.S, a.G, L, h, max 1 (sFrame (fun u => { a.V.div.Nu u with L := L u }) h + a.V.div.RR.muMax), le_max_right _ _, a.V.div.etaF⟩

def Refill.same {a : Late B C} (c : Refill a) : SameGrp a c.to := SameGrp.ofN a.N a.V c.to.V a.S c.S a.G c.G

def Refill.same' {a : Late B C} (c : Refill a) : SameGrp c.to a := SameGrp.ofN a.N c.to.V a.V c.S a.S c.G a.G

namespace Tr

variable {a : Late B C} (c : Refill a) {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type}
variable {Ks : Type} [Field Ks] [NumberField Ks] [iK : Algebra Ks a.D.what₂.LL]

def rowSide {EE : Type} [NormedAddCommGroup EE] [InnerProductSpace ℂ EE] [FiniteDimensional ℂ EE] (X : RowSide a.D EE) :
    RowSide c.to.D EE where
  Amb := (X.Amb)
  instAmb := (X.instAmb)
  instAmbi := (X.instAmbi)
  instAmbf := (X.instAmbf)
  Mult := (X.Mult)
  instMult := (X.instMult)
  instMulti := (X.instMulti)
  instMultf := (X.instMultf)
  multZero := (X.multZero)
  multTop := (X.multTop)
  io := (X.io)
  Mtilde := (X.Mtilde)
  cen := (X.cen)
  eOp := (X.eOp)
  eOp_idem := (X.eOp_idem)
  eOp_sa := (X.eOp_sa)
  eOp_tie := (X.eOp_tie)
  RR := (X.RR)
  RR_frames := (X.RR_frames)
  jEE := (X.jEE)
  jEE_basis := (X.jEE_basis)
  jEE_norm := (X.jEE_norm)

def baseLevelRowSideTransport (X : BaseLevelRowSide a.D) : BaseLevelRowSide c.to.D := ⟨(@rowSide B C a c (@Rows.Data.EE0 (@Late.D B C a).R (@Late.D B C a).what₂) (@Rows.Data.instEE0 (@Late.D B C a).R (@Late.D B C a).what₂) (@Rows.Data.instEE0i (@Late.D B C a).R (@Late.D B C a).what₂) (@Rows.Data.instEE0f (@Late.D B C a).R (@Late.D B C a).what₂) (@BaseLevelRowSide.s (@Late.D B C a) X))⟩

def colReal (K : ColReal a.D) : ColReal c.to.D := ⟨(K.xi)⟩

section Chain

variable {A : FamIn a.D.what₂.LL G Pl0 T a.D.R.m} {R : RealDat a.D A Ks} {F : Face a.D A} {tupT : a.D.what₂.Tup → T}
  {hm : 0 < a.D.R.m} {hTop : TopMultH R}

variable (F tupT hm hTop) in

def spEEc : type_of% (toChainReal R F tupT hm hTop).EEc := ((chainB c.to F tupT hm hTop).EEc)

variable (F tupT hm hTop) in

theorem spEEc_eq : (toChainReal R F tupT hm hTop).EEc = spEEc c F tupT hm hTop := (chain_EEc c.to F tupT hm hTop)

variable (F tupT hm hTop) in

def spCC : type_of% (toChainReal R F tupT hm hTop).CC := ((chainB c.to F tupT hm hTop).CC)

variable (F tupT hm hTop) in

theorem spCC_eq : (toChainReal R F tupT hm hTop).CC = spCC c F tupT hm hTop := (chain_CC c.to F tupT hm hTop)

variable (F tupT hm hTop) in

def spCCP : type_of% (toChainReal R F tupT hm hTop).CCP := ((chainB c.to F tupT hm hTop).CCP)

variable (F tupT hm hTop) in

theorem spCCP_eq : (toChainReal R F tupT hm hTop).CCP = spCCP c F tupT hm hTop := (chain_CCP c.to F tupT hm hTop)

variable (F tupT hm hTop) in

def spCCX : type_of% (toChainReal R F tupT hm hTop).CCX := ((chainB c.to F tupT hm hTop).CCX)

variable (F tupT hm hTop) in

theorem spCCX_eq : (toChainReal R F tupT hm hTop).CCX = spCCX c F tupT hm hTop := (chain_CCX c.to F tupT hm hTop)

variable (F tupT hm hTop) in

def spCCXP : type_of% (toChainReal R F tupT hm hTop).CCXP := ((chainB c.to F tupT hm hTop).CCXP)

variable (F tupT hm hTop) in

theorem spCCXP_eq : (toChainReal R F tupT hm hTop).CCXP = spCCXP c F tupT hm hTop := (chain_CCXP c.to F tupT hm hTop)

variable (F tupT hm hTop) in

def okB (l : Bool) (μ : a.D.what₂.Tup) : Prop := (chainB c.to F tupT hm hTop).IoOK l ((μ))

theorem okB_imp {l : Bool} {μ : a.D.what₂.Tup} (h : okB c F tupT hm hTop l μ) : (toChainReal R F tupT hm hTop).IoOK l μ :=
  chain_ioOK c.to F tupT hm hTop ((h))

theorem eq_via {N : Type} {r : ℂ} (f : N → ℂ) {u u' v : N} (h : r = f u) (e : v = u') (hu : u' = u) : r = f v := by
  rw [e, hu, h]

def ioCB (l : Bool) (μ : a.D.what₂.Tup) (k : ℕ) (v : (toChainReal R F tupT hm hTop).CC l μ (k + 1)) : (toChainReal R F tupT hm hTop).Amb k :=
  (by with_unfolding_all exact (((chainB c.to F tupT hm hTop).ioC l ((by with_unfolding_all exact (μ :))) k
    ((by with_unfolding_all exact ((LinearEquiv.ofEq _ _ (congrFun (congrFun (congrFun (spCC_eq c F tupT hm hTop) l) μ) (k + 1)) v) :)))).1 :))

theorem ioCB_eq (l : Bool) (μ : a.D.what₂.Tup) (k : ℕ) (v : (toChainReal R F tupT hm hTop).CC l μ (k + 1)) :
    ioCB c l μ k v = ((toChainReal R F tupT hm hTop).ioC l μ k v).1 :=
  (by with_unfolding_all exact ((chain_ioC c.to (R := R) (tupT μ) k ((v.1))
    (((LinearEquiv.ofEq _ _ (congrFun (congrFun (congrFun (spCC_eq c F tupT hm hTop) l) μ) (k + 1)) v).2)) ((v.2))) : _))

def ioXB' (l : Bool) (μ : a.D.what₂.Tup) (v : (toChainReal R F tupT hm hTop).CCX l μ) : (toChainReal R F tupT hm hTop).Amb (a.D.R.m - 1) :=
  (by with_unfolding_all exact (((chainB c.to F tupT hm hTop).ioX l ((by with_unfolding_all exact (μ :))) ((by with_unfolding_all exact ((LinearEquiv.ofEq _ _ (congrFun (congrFun (spCCX_eq c F tupT hm hTop) l) μ) v) :)))).1 :))

theorem ioXB'_eq (l : Bool) (μ : a.D.what₂.Tup) (v : (toChainReal R F tupT hm hTop).CCX l μ) :
    ioXB' c l μ v = ((toChainReal R F tupT hm hTop).ioX l μ v).1 :=
  (by with_unfolding_all exact ((chain_ioX c.to (R := R) hm hTop (tupT μ) ((by with_unfolding_all exact (v.1 :))) ((by with_unfolding_all exact ((topMult_tr c.to hTop) :)))
    ((by with_unfolding_all exact ((LinearEquiv.ofEq _ _ (congrFun (congrFun (spCCX_eq c F tupT hm hTop) l) μ) v).2 :))) ((by with_unfolding_all exact (v.2 :)))) :))

end Chain

end Tr

end GlobalTheory.Mem.R3

end
