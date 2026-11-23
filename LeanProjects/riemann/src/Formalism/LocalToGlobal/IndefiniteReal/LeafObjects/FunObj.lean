import Formalism.LocalToGlobal.IndefiniteReal.LeafObjects.MirabolicInclusion
import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.FunctionalLowerBoundOfConditionsNumeric

open Module NumberField IsDedekindDomain

noncomputable section

namespace Formalism.IndefR.Obj

open Formalism.BasicNotions Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.DivisionValues Formalism.IndefR.Links

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

abbrev DfB (R : RealDat D A Ks) (F : Face D A) : DefSide A.fam.base := Formalism.IndefR.Cx.lv (F.fc (R.toCx F).zs) false

structure FunInD (D : D7) {Bs : DefBase D.what₂.LL} (Df : DefSide Bs) where

  n : ℕ

  X' : InfinitePlace D.what₂.LL → Matrix (Fin n) (Fin n) ℂ

  M : Submodule (𝓞 D.what₂.LL) (Fin n → D.what₂.LL)

  vmu : ∀ t : Bs.Tup, Matrix (Fin n) (Fin (Df.nV t)) D.what₂.LL

  Tf : Finset (Pl D.what₂.LL)

  dF : Pl D.what₂.LL → ℤ

  rq : Bs.Tup → Fin D.R.m × Fin D.R.m → D.what₂.LL

  dl : Pl D.what₂.LL → ℝ

  Sd : Finset ℕ

  Se : Finset ℕ

  N0 : Fin D.R.m × Fin D.R.m → ℤ → ℕ → ℝ

  zA : Fin D.R.m × Fin D.R.m → D.what₂.LL
  zA' : Fin D.R.m × Fin D.R.m → D.what₂.LL

  zT : Fin D.R.m × Fin D.R.m → ℤ → D.what₂.LL
  zTd : Fin D.R.m × Fin D.R.m → Bool → ℤ → D.what₂.LL

  gT : Fin D.R.m × Fin D.R.m → ℤ → Pl D.what₂.LL → ℤ

  ch : Pl D.what₂.LL → Bool

  dd : Fin D.R.m × Fin D.R.m → ℕ
  hd : Fin D.R.m × Fin D.R.m → ℕ
  yy : Fin D.R.m × Fin D.R.m → ℕ

  Sq : Type
  S0 : Finset Sq
  sv0 : Sq

  cc : Sq → ℕ
  qq : Sq → ℕ

  Bw : ℝ

def clOf (D : D7) : ℕ → ℕ → ℤ := fun τ i =>
  if hτ : τ < D.R.f then
    if hi : 2 ≤ i ∧ i ≤ D.R.k then
      ⌈(D.hc ((Fintype.equivFinOfCardEq D.what₂.card_Tau).symm ⟨τ, hτ⟩)).v ⟨i - 2, by omega⟩ -
        (D.hc ((Fintype.equivFinOfCardEq D.what₂.card_Tau).symm ⟨τ, hτ⟩)).v
          ⟨D.R.k - 2, by have := D.R.m_add_three_le_k; have := D.R.two_le_m; omega⟩⌉
    else 0
  else 0

abbrev FunIn (R : RealDat D A Ks) (F : Face D A) : Type 1 := FunInD D (DfB R F)

def funMk (D : D7) {Bs : DefBase D.what₂.LL} (Df : DefSide Bs) (J : FunInD D Df) : FunData D.what₂.LL Df where
  n := J.n
  X' := J.X'
  M := J.M
  vmu := J.vmu
  Tf := J.Tf
  dF := J.dF
  m := D.R.m
  rq := J.rq
  dl := J.dl
  Sd := J.Sd
  Se := J.Se
  N0 := J.N0
  zA := J.zA
  zA' := J.zA'
  zT := J.zT
  zTd := J.zTd
  gT := J.gT
  ch := J.ch
  dd := J.dd
  hd := J.hd
  yy := J.yy
  Sq := J.Sq
  S0 := J.S0
  sv0 := J.sv0
  cc := J.cc
  qq := J.qq
  f := D.R.f
  k := D.R.k
  tt := D.R.t
  cl := clOf D
  g1 := D.host.g 0
  g2 := D.host.g 1
  pd := D.host.pde
  pd' := D.host.pde'
  dE := NumberField.discr D.host.E
  Bw := J.Bw

def funObjOf (R : RealDat D A Ks) (F : Face D A) (J : FunIn R F) : FunData D.what₂.LL (DfB R F) :=
  funMk D (DfB R F) J

section Joint

variable (R : RealDat D A Ks) (F : Face D A) (J : FunIn R F)

structure FunLeaves (C : ℝ) : Prop where
  mm : LeafMM (funObjOf R F J) C
  c : LeafC (Sb R F) (funObjOf R F J)
  ker : LeafKer (funObjOf R F J)
  fp : LeafFP (funObjOf R F J) (Sb R F).μ C (F.fc (R.toCx F).zs).Z.b
  ip : LeafIP (Sb R F) (funObjOf R F J) C (F.fc (R.toCx F).zs).Z.b
  oneSquare : LeafOneSquare (funObjOf R F J) (Sb R F).μ C (F.fc (R.toCx F).zs).Z.b
  n0 : PrimeCountingSumBound (funObjOf R F J) C (F.fc (R.toCx F).zs).Z.x (F.fc (R.toCx F).zs).Z.b
  int : LeafINT (funObjOf R F J) C (F.fc (R.toCx F).zs).Z.b
  arch : LeafARCH (funObjOf R F J) C (F.fc (R.toCx F).zs).Z.b
  thb : LeafTHB (funObjOf R F J) C (F.fc (R.toCx F).zs).Z.x (F.fc (R.toCx F).zs).Z.b
  h1 : leafHypothesesConst (funObjOf R F J)
  h7 : LatticeConstantBound (funObjOf R F J) (F.fc (R.toCx F).zs).Z.b
  b5 : DegreeAndSizeBounds (funObjOf R F J) C (F.fc (R.toCx F).zs).Z.b
  b7 : PrimePowerModuliSumBound (funObjOf R F J) C (F.fc (R.toCx F).zs).Z.b
  cs : LeafCS (funObjOf R F J) (F.fc (R.toCx F).zs).Z.b
  wt : LeafWt (funObjOf R F J) C (F.fc (R.toCx F).zs).Z.b

theorem fun_of_leaves (C₀ CH C : ℝ) (wf : (DfB R F).WF) (hD : 0 < (Sb R F).D) (hH0 : (Sb R F).H0)
    (hl1a : (Sb R F).BaseTypeSubspacesMapOntoBothSides) (hl1c : (Sb R F).RowLatticeBoundForBasis) (hXE : ∀ v, IsUnit ((Sb R F).XE v).det)
    (hRR : Submodule.IsLattice D.what₂.LL (Sb R F).RR)
    (hRRw : ∀ w : Pl D.what₂.LL, Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (Sb R F).RR =
      Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (matLat ((Sb R F).ι ((Sb R F).μ w)) ((DfB R F).abelian₂ ((Sb R F).μ w))))
    (hC : 1 ≤ C) (hx : 1 ≤ (F.fc (R.toCx F).zs).Z.x) (hL1 : 1 ≤ Real.log (F.fc (R.toCx F).zs).Z.b)
    (hLx : Real.log (F.fc (R.toCx F).zs).Z.b + Real.log (F.fc (R.toCx F).zs).Z.x ≤
      3 * Real.log (F.fc (R.toCx F).zs).Z.b)
    (hL : FunLeaves R F J C) (hPol : LeafPol (funObjOf R F J) C (F.fc (R.toCx F).zs).Z.x CH (F.fc (R.toCx F).zs).Z.b) :
    R.LFun F C₀ CH :=
  functional_lower_bound_of_conditions_numeric wf (Sb R F) (F.fc (R.toCx F).zs).Z C₀ CH (funObjOf R F J) C hD hH0 hl1a hl1c hXE hRR hRRw hC hx hL1
    hLx hL.mm hL.c hL.ker hL.fp hL.ip hL.oneSquare hL.n0 hL.int hL.arch hL.thb hL.h1 hL.h7 hL.b5 hL.b7 hL.cs hL.wt hPol

end Joint

end Formalism.IndefR.Obj
