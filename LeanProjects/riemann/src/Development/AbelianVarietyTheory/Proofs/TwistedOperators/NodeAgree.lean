import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.NodeYPredEqChainVertexAtRowZeroLast
import Development.AbelianVarietyTheory.Definitions.Divisors.BasePlaceNotMemChiGridBadPlaces

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped Pointwise TensorProduct InnerProductSpace

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.GridJoin

variable {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} {sc : GlobalTheory.ChiGrid.Consts}

structure NodeAgree (N : GlobalTheory.Grid.Node D) {G' : GlobalTheory.ChiGrid.GridData R.toLevCh sc} (W : G'.Weil) (X : GlobalTheory.ChiGrid.Node) :
    Prop where

  sp : N.V = G'.V X

  lat : HEq N.Λ (G'.Λ X)

  cart : HEq (Formalism.IndefR.Links.cart N.M) (W.cart X)

  onb : HEq (Formalism.IndefR.Links.onb N.M) (W.onb X)

structure SpAgree (G : GlobalTheory.Grid.GridPre R) {G' : GlobalTheory.ChiGrid.GridData R.toLevCh sc} (W : G'.Weil) : Prop where

  vert : ∀ i j, i ≤ D.R.m → j ≤ D.R.m → NodeAgree (G.V i j) W (.grid i j)

  core : ∀ i, i ≤ D.R.m → NodeAgree (G.P i) W (.core i)

  top : ∀ j, j ≤ D.R.m → NodeAgree (G.Xp j) W (.top j)

  q0 : G.q0 = GlobalTheory.ChiGrid.q0 D

  w0 : G.w0 = G'.pl.w G'.pl.v0

  e0 : G.e0 = G'.pl.depth sc G'.pl.v0

  places : G.toPlaceDat.W R.Pg = G'.pl.W0

  lvl : G.lvl R = G'.modul

  chiH : ∀ i, 1 ≤ i → i ≤ D.R.m → G.chiH i = G'.ch.chiH i

  chi : ∀ i, 1 ≤ i → i ≤ D.R.m → G.chi i = G'.ch.chi i

structure ArrAgree (G : GlobalTheory.Grid.GridPre R) {G' : GlobalTheory.ChiGrid.GridData R.toLevCh sc} (W : G'.Weil) : Prop where

  omX : ∀ i j, i < D.R.m → j ≤ D.R.m → HEq ((G.X i j).ω.toSgn true) (W.om (.chi i j))

  omT : ∀ t i j, i ≤ D.R.m → j < D.R.m → HEq (G.th t i j).ω (W.om (.mu t i j))

  omC : ∀ t j, j < D.R.m → HEq (G.col t j).ω (W.om (.top t j))

  omD : ∀ i, i < D.R.m → HEq ((G.dn i).ω.toSgn true) (W.om (.core i))

  vacX : ∀ i, i < D.R.m → HEq (G.X i 0).vac (W.vac i)

  cos : ∀ i, i < D.R.m → (∀ c, ∃ κ, HEq (G.vC i c) (W.cosVec i κ)) ∧ ∀ κ, ∃ c, HEq (G.vC i c) (W.cosVec i κ)

def Agree (G : GlobalTheory.Grid.GridPre R) {G' : GlobalTheory.ChiGrid.GridData R.toLevCh sc} (W : G'.Weil) : Prop :=
  SpAgree G W ∧ ArrAgree G W

end GlobalTheory.GridJoin

namespace GlobalTheory.GridJoin

open GlobalTheory.Grid

variable {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks}

def withArr (G : GridPre R) (X : ∀ i j, ArrS (G.V (i + 1) j) (G.V i j))
    (ωT : T → ∀ i j, WRep (G.nV i j).V (G.nV i (j + 1)).V) (vacT : ∀ i j, WO (G.nV i j).V (G.nV i (j + 1)).V → ℂ)
    (ItT : ∀ i j, Pol (G.nV i j) (G.nV i (j + 1)) →ₗ[ℂ] SmT (G.nV i (j + 1)).M →ₗ[ℂ] SmT (G.nV i j).M)
    (ωC : T → ∀ j, WRep (G.Xp j).V (G.nX j).V) (vacC : ∀ j, WO (G.Xp j).V (G.nX j).V → ℂ)
    (ItC : ∀ j, Pol (G.Xp j) (G.nX j) →ₗ[ℂ] SmT (G.Xp j).M →ₗ[ℂ] SmT (G.nX j).M)
    (dn : ∀ i, ArrT (G.P (i + 1)) (G.P i))
    (ItU : ∀ i, Pol (G.P (i + 1)) (G.P i) →ₗ⋆[ℂ] SmT (G.P i).M →ₗ[ℂ] SmT (G.P (i + 1)).M)
    (vC : ∀ i, G.toGridSp.Cos R i → (WO (G.V (i + 1) 0).V (G.V i 0).V → ℂ)) : GridPre R :=
  { G with X := X, ωT := ωT, vacT := vacT, ItT := ItT, ωC := ωC, vacC := vacC, ItC := ItC, dn := dn, ItU := ItU, vC := vC }

def withMeas (G : GridPre R) (m00 : (G.V 0 0).MeasDat) (mV : ∀ i j, (G.nV i j).MeasDat) (mP : ∀ i, (G.P i).MeasDat)
    (mX : ∀ j, (G.nX j).MeasDat) : GridPre R :=
  { G with m00 := m00, mV := mV, mP := mP, mX := mX }

end GlobalTheory.GridJoin
