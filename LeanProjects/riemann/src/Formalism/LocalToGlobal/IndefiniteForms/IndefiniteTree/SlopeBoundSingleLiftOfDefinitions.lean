import Mathlib
import Formalism.LocalToGlobal.IndefiniteForms.IndefSide
import Formalism.LocalToGlobal.IndefiniteForms.IndefUse
import Formalism.LocalToGlobal.IndefiniteForms.IndefExample
import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.IndefiniteTreeX
import Formalism.MeanHeightDescent.DivisionInequalityWithCovolume
import Formalism.MeanHeightDescent.CovolumeFullAssemblyWeighted
import Formalism.ThetaSupremumBounds.LiftOperatorBoundOfFockJet

open Finset Module NumberField Formalism.HN

noncomputable section

namespace Formalism.L2.Indef.Tree

structure SlopeBoundParameters where

  Pl : Type

  fPl : Fintype Pl

  x : ℝ

  eps : ℝ

  rd : ℝ

  v : ℝ

  dN : ℕ

  dimNeZero : NeZero dN

  χ : DirichletCharacter ℂ dN

  Z : ℝ

  logOmK : ℝ

  logOm : ℝ

  f : ℝ

  m : ℝ

  k : ℝ

  S : ℝ

  η : ℝ

  R : ℝ

  PPp : ℝ

  PPpp : ℝ

  PP : ℝ

  PPT : ℝ

  Zpg : ℝ

  nV : ℝ

  Nr : ℝ

  g12 : ℝ

attribute [instance] SlopeBoundParameters.fPl SlopeBoundParameters.dimNeZero

def LcOf {n : ℕ} [NeZero n] (χ : DirichletCharacter ℂ n) : ℝ :=
  (deriv (DirichletCharacter.LFunction χ) 1 / DirichletCharacter.LFunction χ 1).re

def leadingConstant {n : ℕ} [NeZero n] (χ : DirichletCharacter ℂ n) : ℝ :=
  (deriv (DirichletCharacter.LFunction χ) 0 / DirichletCharacter.LFunction χ 0).re

def eulerConstantTerm (n : ℕ) : ℝ :=
  (∑ q ∈ reducedForms (-(n : ℤ)), Real.log (4 * Real.pi * (formRoot (-(n : ℤ)) q).im *
    ‖ModularForm.eta (formRoot (-(n : ℤ)) q)‖ ^ 4)) / ((reducedForms (-(n : ℤ))).card : ℝ)

namespace SlopeBoundParameters

variable (P : SlopeBoundParameters)

def L : ℝ := P.x ^ P.eps

def b : ℝ := Real.exp P.L

def a : ℝ := P.x * P.b

def La : ℝ := Real.log (P.a * P.rd)

def lrd : ℝ := Real.log P.rd

def llx : ℝ := Real.log (Real.log P.x)

def dK : ℝ := (P.dN : ℝ)

def Lc : ℝ := LcOf P.χ

def L0 : ℝ := leadingConstant P.χ

def A1 : ℝ := eulerConstantTerm P.dN

def LL0 : ℝ := Real.log (P.b * P.rd) * P.llx + |P.Lc| + Real.log P.x

def B0 : ℝ := P.f * P.m * P.b * P.x ^ P.eps

end SlopeBoundParameters

structure SlopeBoundLiftData (K : Type) [Field K] [NumberField K] [StarRing K] (P : SlopeBoundParameters) where

  w : P.Pl → ℝ

  w0 : P.Pl → ℝ

  c1 : P.Pl → ℝ

  ua : P.Pl → ℝ

  kap : ℝ

  q' : ℕ

  pq : ℝ

  ι : Type

  fι : Fintype ι

  nι : Nonempty ι

  DY : ℝ

  A : ℝ

  cs : ℝ

  X : ℝ

  cc : ℝ

  E0 : ℝ

  Qcc : ℝ

  ρ : ℝ

  R1 : ℝ

  R2 : ℝ

  Bn : ℝ

  δ' : ℝ

  h : ι → ℝ

  sl : ι → ℝ

  δc : ι → ℝ

  dc : ι → ℝ

  degc : ι → ℝ

  PPf : ℝ

  mv : ℝ

  muU : ℝ

  nA : ℕ

  nB : ℕ

  nN : ℕ

  XA : InfinitePlace K → Matrix (Fin nA) (Fin nA) ℂ

  XB : InfinitePlace K → Matrix (Fin nB) (Fin nB) ℂ

  XN : InfinitePlace K → Matrix (Fin nN) (Fin nN) ℂ

  LA : Submodule (𝓞 K) (Fin nA → K)

  LB : Submodule (𝓞 K) (Fin nB → K)

  NN : Submodule (𝓞 K) (Fin nN → K)

  Mk : Submodule (𝓞 K) (Fin nN → K)

  φ : (Fin nA → K) →ₗ[K] (Fin nB → K)

  e : (Fin nN → K) →ₗ[K] (Fin nN → K)

  g : ℕ

  PPh : ℝ

  abelian₂ : ℝ

  δ : ℝ

  o' : ℝ

  n2 : ℝ

attribute [instance] SlopeBoundLiftData.fι SlopeBoundLiftData.nι

namespace SlopeBoundLiftData

variable {K : Type} [Field K] [NumberField K] [StarRing K] {P : SlopeBoundParameters} (F : SlopeBoundLiftData K P)

def T : ℝ := ((⌈P.PPT ^ 2 * F.DY ^ 2 * P.k / P.m⌉ : ℤ) : ℝ)

def ε : ℝ := 7 * F.DY ^ 2 / F.T + 3 / 2 * F.DY * F.ρ

def z : ℝ := 7 * (F.DY ^ 2 / F.T + F.DY * F.ρ)

def U : ℝ := ∑ τ, F.ua τ

def Q : ℝ := 2 * (P.PPp + 1 + P.lrd) * F.kap

def cfl (Cf : ℝ) : ℝ :=
  (∑ τ, F.w τ * F.c1 τ) - Cf * F.q' * Real.log P.rd * (∑ τ, F.w τ) - Cf * P.L

def e1 (Ca : ℝ) : ℝ := Ca * P.LL0 * F.E0

def e2 (Cb : ℝ) : ℝ := Cb * P.LL0 * F.E0 + F.T * F.Qcc

def main : ℝ := ∑ σ, F.pq * F.w0 σ * P.logOm

def muA : ℝ := muDef (Pi.basisFun K (Fin F.nA)) F.XA F.LA

def muN : ℝ := muDef (Pi.basisFun K (Fin F.nN)) F.XN F.NN

def good : Submodule (𝓞 K) (Fin F.nN → K) := F.NN ⊓ (LinearMap.range F.e).restrictScalars (𝓞 K)

def bad : Submodule (𝓞 K) (Fin F.nN → K) := F.NN ⊓ (LinearMap.ker F.e).restrictScalars (𝓞 K)

def muG : ℝ := muDef (Pi.basisFun K (Fin F.nN)) F.XN F.good

def mmax : ℝ := muMaxDef (Pi.basisFun K (Fin F.nN)) F.XN F.Mk

end SlopeBoundLiftData

def slopeBoundConstant (Ca Cb Cf Cc C1 Cm : ℝ) : ℝ := 64 * (Ca + Cb + C1 + 3 * Cf) + 8 * Cc + 14 + Cm

def LeafKL (P : SlopeBoundParameters) : Prop :=
  P.Z = Real.log (2 / Real.sqrt P.dK) + (P.A1 + Real.log Real.pi)

def LeafCN (P : SlopeBoundParameters) : Prop :=
  P.Z = Real.log (2 * Real.pi) + P.L0

def LeafFE (P : SlopeBoundParameters) : Prop :=
  P.L0 = -P.Lc - Real.log (P.dK / Real.pi) + Real.eulerMascheroniConstant + Real.log 2

def LeafDiff (P : SlopeBoundParameters) : Prop :=
  P.logOmK = P.A1

def LeafNorm (P : SlopeBoundParameters) : Prop :=
  P.logOm = P.logOmK - Real.log P.rd + Real.log (Real.sqrt P.dK)

section Leaves

variable {K : Type} [Field K] [NumberField K] [StarRing K] {P : SlopeBoundParameters}

def LeafDegFlat (Cc : ℝ) (F : SlopeBoundLiftData K P) : Prop :=
  ∀ τ, |F.c1 τ + F.pq * P.logOm / 2| ≤ Cc * F.q' * Real.log P.rd

def LeafExport (Cf : ℝ) (F : SlopeBoundLiftData K P) : Prop :=
  |(∑ τ, F.w τ * F.c1 τ) - Cf * F.q' * Real.log P.rd * (∑ τ, F.w τ)| ≤ P.PPp * F.kap

def LeafRoot (F : SlopeBoundLiftData K P) : Prop :=
  0 ≤ F.mv ∧ F.mv ≤ P.b / 50

def LeafFlat (Cf : ℝ) (F : SlopeBoundLiftData K P) : Prop :=
  F.muU - 2 * F.mv + 2 * F.cfl Cf ≤ F.muA

def LeafDeg (F : SlopeBoundLiftData K P) : Prop :=
  ∀ c, F.δ' ≤ F.δc c ∧ F.δc c ≤ F.δ' / (1 - F.ρ)

def LeafRho (F : SlopeBoundLiftData K P) : Prop :=
  0 ≤ F.ρ

def LeafShare (F : SlopeBoundLiftData K P) : Prop :=
  ∀ c, F.Bn * F.δc c ≤ F.dc c ∧ (1 - F.z) * F.dc c ≤ F.Bn * F.δc c

def LeafSmall (F : SlopeBoundLiftData K P) : Prop :=
  (∀ c, 0 ≤ F.h c + F.cs) ∧ 0 ≤ F.cc ∧ ∀ c, (1 - F.ρ) * max 0 (F.sl c + F.cs) ≤ F.h c + F.cs + F.cc

def LeafMeans (Ca Cb : ℝ) (F : SlopeBoundLiftData K P) : Prop :=
  0 ≤ F.X ∧ -F.X ≤ (∑ c, F.sl c) / (Fintype.card F.ι : ℝ) ∧
    F.T * F.X ≤ Ca * P.LL0 * (F.U + F.E0) ∧ F.T * F.cc ≤ Cb * P.LL0 * (F.U + F.E0) + F.T * F.Qcc

def LeafHS (F : SlopeBoundLiftData K P) : Prop :=
  0 < F.A ∧ 0 ≤ F.R1 ∧ 0 ≤ F.R2 ∧
    ∀ c, F.Bn * F.δc c * (F.T * F.h c - 3 * (F.DY + 1) * |F.h c| - F.A * Real.log (2 + |F.h c|) - F.R1 -
      2 * F.z * F.R2) ≤ F.degc c

def LeafSum (F : SlopeBoundLiftData K P) : Prop :=
  2 * ((∑ c, F.degc c) / (∑ c, F.dc c) - F.PPf) ≤ F.muU

def CrudeSizeBound (F : SlopeBoundLiftData K P) : Prop :=
  F.cs ≤ P.PPp * (F.kap / F.T + 1)

def LeafEps (F : SlopeBoundLiftData K P) : Prop :=
  F.ε * ((P.PPp + 1 + Real.log P.rd) * F.kap) ≤ P.b / 8

def LeafDescent (F : SlopeBoundLiftData K P) : Prop :=
  F.LA.FG ∧ F.LB.FG ∧ F.NN.FG ∧ F.LA ≠ ⊥ ∧ F.NN ≠ ⊥ ∧
    (∀ v, IsUnit (F.XA v).det) ∧ (∀ v, IsUnit (F.XB v).det) ∧
    Function.Injective F.φ ∧ F.LA.map (F.φ.restrictScalars (𝓞 K)) ≤ F.LB ∧
    htMap (Pi.basisFun K (Fin F.nA)) F.XA (Pi.basisFun K (Fin F.nB)) F.XB F.φ ≤ 2 * F.PPh ∧ 0 ≤ F.PPh ∧
    muDef (Pi.basisFun K (Fin F.nB)) F.XB F.LB = F.muN ∧
    muMinDef (Pi.basisFun K (Fin F.nB)) F.XB F.LB = muMinDef (Pi.basisFun K (Fin F.nN)) F.XN F.NN ∧
    rkK F.LA ≤ rkK F.LB ∧ (1 - F.ε) * (rkK F.LB : ℝ) ≤ (rkK F.LA : ℝ) ∧
    ∃ s : Set (Fin F.nN → K), s ⊆ (F.NN : Set (Fin F.nN → K)) ∧
      (∀ y ∈ s, ∀ v, Formalism.HermitianLatticesTheory.normAt (Pi.basisFun K (Fin F.nN)) F.XN v y ≤ Real.exp F.abelian₂) ∧
      (F.NN : Set (Fin F.nN → K)) ⊆ (Submodule.span K s : Set (Fin F.nN → K))

def LeafPh (F : SlopeBoundLiftData K P) : Prop :=
  F.PPh ≤ P.PPpp

def LeafGmin (F : SlopeBoundLiftData K P) : Prop :=
  F.abelian₂ ≤ P.PPp * F.kap

def LeafLam (F : SlopeBoundLiftData K P) : Prop :=
  F.mmax ≤ 2 * P.PPp * F.kap

def LeafCut (F : SlopeBoundLiftData K P) : Prop :=
  F.NN.FG ∧ F.Mk.FG ∧ F.NN ≠ ⊥ ∧ (∀ v, IsUnit (F.XN v).det) ∧ 1 ≤ F.g ∧ F.e ∘ₗ F.e = F.e ∧
    (∀ v y y', Formalism.HermitianLatticesTheory.majAt (Pi.basisFun K (Fin F.nN)) F.XN v (F.e y) y' =
      Formalism.HermitianLatticesTheory.majAt (Pi.basisFun K (Fin F.nN)) F.XN v y (F.e y')) ∧
    (∀ y ∈ F.NN, ((F.g : ℕ) : K) • F.e y ∈ F.NN) ∧ F.NN ≤ F.Mk ∧
    Real.log F.g ≤ 20 * P.f * P.Nr ^ 2 * P.L

def LeafShareBad (F : SlopeBoundLiftData K P) : Prop :=
  0 ≤ F.δ ∧ F.δ ≤ Real.exp (-(P.x ^ (P.eps / 7)))

def LeafBadRows (F : SlopeBoundLiftData K P) : Prop :=
  (rkK F.bad : ℝ) ≤ 3 * F.δ * (rkK F.NN : ℝ)

def LeafMuN (F : SlopeBoundLiftData K P) : Prop :=
  |F.muN| ≤ 2 * P.PPp * F.kap

def LeafRecord {d : ℕ} (XWr : InfinitePlace K → Matrix (Fin d) (Fin d) ℂ) (M : Submodule (𝓞 K) (Fin d → K))
    (F : SlopeBoundLiftData K P) : Prop :=
  F.muG - 2 * (F.o' + F.n2) ≤ muDef (Pi.basisFun K (Fin d)) XWr M ∧ F.o' ≤ P.PPpp

def LeafNote2 (Cn : ℝ) (F : SlopeBoundLiftData K P) : Prop :=
  0 ≤ F.n2 ∧ F.n2 ≤ Cn * P.f * P.Nr ^ 2 * Real.log (P.Nr * P.rd * P.g12)

def LeafDef (C1 Cf : ℝ) (F : SlopeBoundLiftData K P) : Prop :=
  (∑ τ, F.w τ * F.c1 τ) - C1 * P.LL0 * F.U - P.PP - (2 * P.Zpg * P.nV + Cf * P.L) ≤ F.muN / 2

def LeafMeasure (Cm : ℝ) {D d : ℕ} (XW XWr : InfinitePlace K → Matrix (Fin d) (Fin d) ℂ)
    (M : Submodule (𝓞 K) (Fin d → K)) : SlopeBoundParameters → Prop := fun P =>
  (∀ v, IsUnit (XWr v).det) ∧ Formalism.DivisionValues.lcv XW M / (D : ℝ) ≤ Formalism.DivisionValues.lcv XWr M / (D : ℝ) + Cm * P.B0

end Leaves

def PageParams (P : SlopeBoundParameters) : Prop :=
  (∀ n : ℕ, P.χ n = ((jacobiSym n P.dN : ℤ) : ℂ)) ∧ P.χ.IsPrimitive ∧ P.χ.Odd ∧
  1 ≤ P.x ∧ 0 < P.eps ∧ 4 ≤ P.rd ∧ 2 * P.v = P.rd ∧ 0 < P.v ∧ Real.log P.rd ≤ P.L ∧ |P.Lc| ≤ P.L ∧
  Real.log P.x ≤ P.L ∧ 1 ≤ P.llx ∧ 3 ≤ P.x ^ (P.eps / 7) ∧
  (Fintype.card P.Pl : ℝ) ≤ P.f ∧ 1 ≤ P.m ∧ 1 ≤ P.f ∧ 1 ≤ P.k ∧ P.k * P.S ≤ P.b ∧ P.k * P.η ≤ P.b ∧
  0 ≤ P.S ∧ 0 ≤ P.R ∧ P.k * P.R ≤ P.b ∧
  20 * P.f * P.Nr ^ 2 * P.L ≤ P.PPp ∧ P.PPpp ≤ P.b / 8 ∧ P.PP + 2 * P.Zpg * P.nV ≤ P.b / 4

def FacParams {K : Type} [Field K] [NumberField K] [StarRing K] (Cf : ℝ) {P : SlopeBoundParameters} (F : SlopeBoundLiftData K P) : Prop :=
  (∀ τ, P.m * F.w τ / 2 ≤ F.ua τ ∧ F.ua τ ≤ 2 * (P.m * F.w τ + P.k * P.S + P.k * P.η)) ∧ 1 ≤ F.U ∧
  (∀ τ, 0 ≤ F.w τ ∧ F.w τ ≤ 2 * P.b) ∧ (∀ σ, |F.w σ - F.w0 σ| ≤ P.S + P.R) ∧ |F.pq - P.k| ≤ P.m ∧
  0 ≤ (F.q' : ℝ) ∧ (F.q' : ℝ) ≤ P.m ∧ 1 ≤ F.kap ∧ Cf * P.L ≤ F.kap ∧
  24 * F.δ * ((P.PPp + 1 + Real.log P.rd) * F.kap) ≤ P.b / 8 ∧ 2 * F.n2 ≤ P.b / 8

def CompParams {K : Type} [Field K] [NumberField K] [StarRing K] (Ca Cb : ℝ) {P : SlopeBoundParameters} (F : SlopeBoundLiftData K P) : Prop :=
  2 ≤ F.DY ∧ 20 * F.DY ≤ F.T ∧ F.DY ^ 2 / F.T ≤ 1 / 28 ∧ F.DY * F.ρ ≤ 1 / 28 ∧ 0 ≤ F.cs ∧ 0 < F.Bn ∧ 0 < F.δ' ∧
  F.cs * (6 * F.DY + 10 + F.T * (F.z + 2 * F.ρ)) + (F.A * Real.log (max F.A 1) + 4) + F.R1 + 2 * F.z * F.R2 +
    F.PPf + F.e1 Ca + F.e2 Cb ≤ P.b / 8

theorem descent_cut_lines (K V ι W κ V2 ι2 : Type) [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K]
    [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [Fintype ι]
    [DecidableEq ι] [AddCommGroup W] [Module K W] [Module (𝓞 K) W] [IsScalarTower (𝓞 K) K W]
    [Fintype κ] [DecidableEq κ] [AddCommGroup V2] [Module K V2] [Module (𝓞 K) V2]
    [IsScalarTower (𝓞 K) K V2] [Fintype ι2] [DecidableEq ι2]
    (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ)
    (b' : Basis κ K W) (X' : InfinitePlace K → Matrix κ κ ℂ)
    (b2 : Basis ι2 K V2) (X2 : InfinitePlace K → Matrix ι2 ι2 ℂ)
    (hX : ∀ v, IsUnit (X v).det) (hX' : ∀ v, IsUnit (X' v).det) (hX2 : ∀ v, IsUnit (X2 v).det)
    (φ : V →ₗ[K] W) (A : Submodule (𝓞 K) V) (B : Submodule (𝓞 K) W)
    (N Mb : Submodule (𝓞 K) V2) (e : V2 →ₗ[K] V2) (g : ℕ) (P Λ : ℝ)
    (hA : A.FG) (hB : B.FG) (hN : N.FG) (hMb : Mb.FG) (hA0 : A ≠ ⊥) (hN0 : N ≠ ⊥)
    (hinj : Function.Injective φ) (hmap : A.map (φ.restrictScalars (𝓞 K)) ≤ B) (hht : htMap b X b' X' φ ≤ P)
    (hmuB : muDef b' X' B = muDef b2 X2 N) (hminB : muMinDef b' X' B = muMinDef b2 X2 N)
    (hrk : rkK A ≤ rkK B)
    (hspan : ∃ s : Set V2, s ⊆ (N : Set V2) ∧ (∀ x ∈ s, ∀ v, Formalism.HermitianLatticesTheory.normAt b2 X2 v x ≤ Real.exp Λ) ∧
        (N : Set V2) ⊆ (Submodule.span K s : Set V2))
    (hg : 1 ≤ g) (hee : e ∘ₗ e = e)
    (hsa : ∀ v x y, Formalism.HermitianLatticesTheory.majAt b2 X2 v (e x) y = Formalism.HermitianLatticesTheory.majAt b2 X2 v x (e y))
    (hint : ∀ x ∈ N, (g : K) • e x ∈ N) (hNM : N ≤ Mb) :
    (0 : ℝ) < (rkK A : ℝ) ∧ (rkK A : ℝ) ≤ (rkK B : ℝ) ∧
    (rkK A : ℝ) * (muDef b X A - P) + ((rkK B : ℝ) - (rkK A : ℝ)) * (-(2 * Λ)) ≤ (rkK B : ℝ) * muDef b2 X2 N ∧
    (0 : ℝ) < (rkK N : ℝ) ∧
    (rkK N : ℝ) = (rkK (N ⊓ (LinearMap.range e).restrictScalars (𝓞 K)) : ℝ) +
      (rkK (N ⊓ (LinearMap.ker e).restrictScalars (𝓞 K)) : ℝ) ∧
    (0 : ℝ) ≤ (rkK (N ⊓ (LinearMap.ker e).restrictScalars (𝓞 K)) : ℝ) ∧
    (rkK N : ℝ) * muDef b2 X2 N ≤
      (rkK (N ⊓ (LinearMap.range e).restrictScalars (𝓞 K)) : ℝ) *
        muDef b2 X2 (N ⊓ (LinearMap.range e).restrictScalars (𝓞 K)) +
      (rkK (N ⊓ (LinearMap.ker e).restrictScalars (𝓞 K)) : ℝ) * (muMaxDef b2 X2 Mb + 2 * Real.log g) := by
  have hDS := Formalism.ExtensionFiltration.descentSlope K V ι W κ b X b' X' hX hX' φ A B hA hB hA0 hinj hmap
  have hSM := Formalism.ExtensionFiltration.spanMuMin K V2 ι2 b2 X2 hX2 N Λ hN hN0 hspan
  obtain ⟨hr, hdeg, hmax⟩ := Formalism.ExtensionFiltration.goodBadCut K V2 ι2 b2 X2 hX2 e g N hN hg hee hsa hint
  have hmax' := hmax Mb hMb hNM
  have hrA : (0 : ℝ) < (rkK A : ℝ) := by exact_mod_cast Formalism.ExtensionFiltration.rkK_pos b A hA0
  have hrN : (0 : ℝ) < (rkK N : ℝ) := by exact_mod_cast Formalism.ExtensionFiltration.rkK_pos b2 N hN0
  have hrAB : (rkK A : ℝ) ≤ (rkK B : ℝ) := by exact_mod_cast hrk
  rw [hmuB, hminB] at hDS
  have e1 : (rkK A : ℝ) * (muDef b X A - P) ≤ (rkK A : ℝ) * (muDef b X A - htMap b X b' X' φ) :=
    mul_le_mul_of_nonneg_left (by linarith) hrA.le
  have e2 : ((rkK B : ℝ) - (rkK A : ℝ)) * (-(2 * Λ)) ≤ ((rkK B : ℝ) - (rkK A : ℝ)) * muMinDef b2 X2 N :=
    mul_le_mul_of_nonneg_left hSM (by linarith)
  have hsum : (rkK N : ℝ) = (rkK (N ⊓ (LinearMap.range e).restrictScalars (𝓞 K)) : ℝ) +
      (rkK (N ⊓ (LinearMap.ker e).restrictScalars (𝓞 K)) : ℝ) := by exact_mod_cast hr.symm
  refine ⟨hrA, hrAB, by linarith, hrN, hsum, by positivity, by nlinarith⟩

theorem cut_lines (K V2 ι2 : Type) [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K]
    [AddCommGroup V2] [Module K V2] [Module (𝓞 K) V2] [IsScalarTower (𝓞 K) K V2] [Fintype ι2] [DecidableEq ι2]
    (b2 : Basis ι2 K V2) (X2 : InfinitePlace K → Matrix ι2 ι2 ℂ) (hX2 : ∀ v, IsUnit (X2 v).det)
    (N Mb : Submodule (𝓞 K) V2) (e : V2 →ₗ[K] V2) (g : ℕ)
    (hN : N.FG) (hMb : Mb.FG) (hN0 : N ≠ ⊥) (hg : 1 ≤ g) (hee : e ∘ₗ e = e)
    (hsa : ∀ v x y, Formalism.HermitianLatticesTheory.majAt b2 X2 v (e x) y = Formalism.HermitianLatticesTheory.majAt b2 X2 v x (e y))
    (hint : ∀ x ∈ N, (g : K) • e x ∈ N) (hNM : N ≤ Mb) :
    (0 : ℝ) < (rkK N : ℝ) ∧
    (rkK N : ℝ) = (rkK (N ⊓ (LinearMap.range e).restrictScalars (𝓞 K)) : ℝ) +
      (rkK (N ⊓ (LinearMap.ker e).restrictScalars (𝓞 K)) : ℝ) ∧
    (0 : ℝ) ≤ (rkK (N ⊓ (LinearMap.ker e).restrictScalars (𝓞 K)) : ℝ) ∧
    (rkK N : ℝ) * muDef b2 X2 N ≤
      (rkK (N ⊓ (LinearMap.range e).restrictScalars (𝓞 K)) : ℝ) *
        muDef b2 X2 (N ⊓ (LinearMap.range e).restrictScalars (𝓞 K)) +
      (rkK (N ⊓ (LinearMap.ker e).restrictScalars (𝓞 K)) : ℝ) * (muMaxDef b2 X2 Mb + 2 * Real.log g) := by
  obtain ⟨hr, hdeg, hmax⟩ := Formalism.ExtensionFiltration.goodBadCut K V2 ι2 b2 X2 hX2 e g N hN hg hee hsa hint
  have hmax' := hmax Mb hMb hNM
  have hrN : (0 : ℝ) < (rkK N : ℝ) := by exact_mod_cast Formalism.ExtensionFiltration.rkK_pos b2 N hN0
  have hsum : (rkK N : ℝ) = (rkK (N ⊓ (LinearMap.range e).restrictScalars (𝓞 K)) : ℝ) +
      (rkK (N ⊓ (LinearMap.ker e).restrictScalars (𝓞 K)) : ℝ) := by exact_mod_cast hr.symm
  refine ⟨hrN, hsum, by positivity, by nlinarith⟩

theorem period_of_leaves (P : SlopeBoundParameters) (hKL : LeafKL P) (hCN : LeafCN P) (hFE : LeafFE P) (hDi : LeafDiff P)
    (hNo : LeafNorm P) (hv : 0 < P.v) (hrd : 2 * P.v = P.rd) (h4 : 4 ≤ P.rd) (hLc : |P.Lc| ≤ P.L)
    (hx : 1 ≤ P.x) :
    P.logOm = Real.eulerMascheroniConstant + Real.log (Real.pi / P.v) - P.Lc ∧ |P.logOm| ≤ P.La := by
  have hd : 0 < P.dK := by
    unfold SlopeBoundParameters.dK; exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne P.dN)
  have hval := (Formalism.DimensionVariation.periodValue P.dK P.v P.rd P.A1 P.Z P.L0 P.Lc P.logOmK P.logOm hd hv hrd.symm
    hKL hCN hFE hDi hNo).2.2
  exact ⟨hval, Formalism.ExtensionFiltration.periodBound P.logOm P.v P.rd P.Lc P.L P.x P.b P.a hval hrd h4 hLc hx rfl rfl⟩

theorem exp_neg_le_twelfth (t : ℝ) (ht : 3 ≤ t) : Real.exp (-t) ≤ 1 / 12 := by
  have h1 : (2.7 : ℝ) < Real.exp 1 := lt_trans (by norm_num) Real.exp_one_gt_d9
  have h3 : Real.exp 3 = Real.exp 1 ^ 3 := by rw [← Real.exp_nat_mul]; norm_num
  have h27 : (2.7 : ℝ) ^ 3 ≤ Real.exp 1 ^ 3 := pow_le_pow_left₀ (by norm_num) h1.le 3
  have h12 : 12 ≤ Real.exp 3 := by rw [h3]; linarith [show (12 : ℝ) ≤ 2.7 ^ 3 by norm_num]
  have hm : Real.exp (-t) ≤ Real.exp (-3) := Real.exp_le_exp.mpr (by linarith)
  have e3 : Real.exp (-3) * Real.exp 3 = 1 := by rw [← Real.exp_add]; norm_num
  have hp : 0 < Real.exp (-3) := Real.exp_pos _
  nlinarith

theorem cfl_Q (E CfL PPp kap lrdk : ℝ) (hE : |E| ≤ PPp * kap) (h0 : 0 ≤ CfL) (h1 : CfL ≤ kap) (hl : 0 ≤ lrdk) :
    |2 * (E - CfL)| ≤ 2 * (PPp * kap) + 2 * kap + 2 * lrdk := by
  rw [abs_le] at hE ⊢; constructor <;> linarith

theorem g_Q (lg a PPp kap : ℝ) (h1 : lg ≤ a) (h2 : a ≤ PPp) (hk : 1 ≤ kap) (hP : 0 ≤ PPp) :
    2 * lg ≤ 2 * PPp * kap := by nlinarith

set_option maxHeartbeats 1000000 in

theorem slope_bound_single_lift_of_definitions {K : Type} [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K]
    (Ca Cb Cf Cc C1 Cm Cn : ℝ) (hCa : 0 ≤ Ca) (hCb : 0 ≤ Cb) (hCf : 0 ≤ Cf) (hCc : 0 ≤ Cc) (hC1 : 0 ≤ C1)
    (hCm : 0 ≤ Cm) (d D : ℕ) (hD : 0 < D) (hdD : d = D) (XW XWr : InfinitePlace K → Matrix (Fin d) (Fin d) ℂ)
    (M : Submodule (𝓞 K) (Fin d → K)) (hM : Submodule.IsLattice K M) (P : SlopeBoundParameters) (F : SlopeBoundLiftData K P)
    (hKL : LeafKL P) (hCN : LeafCN P) (hFE : LeafFE P) (hDi : LeafDiff P) (hNo : LeafNorm P)
    (hPg : PageParams P) (hFa : FacParams Cf F) (hDF : LeafDegFlat Cc F) (hEx : LeafExport Cf F)
    (hCu : LeafCut F) (hSB : LeafShareBad F) (hBR : LeafBadRows F) (hMN : LeafMuN F) (hLa : LeafLam F)
    (hRe : LeafRecord XWr M F) (hN2 : LeafNote2 Cn F) (hMe : LeafMeasure Cm (D := D) XW XWr M P)
    (hq : F.q' = 0) (hDe : LeafDef C1 Cf F) :
    Formalism.DivisionValues.lcv XW M / (D : ℝ) ≤ F.main + slopeBoundConstant Ca Cb Cf Cc C1 Cm * (P.B0 * P.llx) := by
  obtain ⟨-, -, -, hx, heps, hrd4, hv2, hv, hlrd, hLc, hlx, hllx, hx7, hcard, hm, hf, hk, hkS, hkη, hS, hR, hkR,
    hGP, hPPpp, hPPdef⟩ := hPg
  obtain ⟨hwt, hU, hw, hsh, hpq, hq0, hq1, hkap, hCLk, hδb, hn2b⟩ := hFa
  obtain ⟨-, hper⟩ := period_of_leaves P hKL hCN hFE hDi hNo hv hv2 hrd4 hLc hx
  obtain ⟨hNfg, hMkfg, hN0, hXN, hg1, hee, hsa, hint, hNM, hlogg⟩ := hCu
  obtain ⟨hδ0, hδx⟩ := hSB
  obtain ⟨hXWr, hmes⟩ := hMe
  obtain ⟨hrec, ho'⟩ := hRe
  obtain ⟨hn20, -⟩ := hN2

  have hL0 : 0 ≤ P.L := Real.rpow_nonneg (by linarith) _
  have hb1 : 1 ≤ P.b := Real.one_le_exp hL0
  have hlrd0 : 0 ≤ Real.log P.rd := Real.log_nonneg (by linarith)
  have hδ12 : F.δ ≤ 1 / 12 := le_trans hδx (exp_neg_le_twelfth _ hx7)
  have hkap0 : 0 ≤ F.kap := by linarith
  have hfN : 0 ≤ 20 * P.f * P.Nr ^ 2 * P.L := by positivity
  have hPPp0 : 0 ≤ P.PPp := by linarith
  have hQe : F.Q = 2 * (P.PPp * F.kap) + 2 * F.kap + 2 * (Real.log P.rd * F.kap) := by
    unfold SlopeBoundLiftData.Q SlopeBoundParameters.lrd; ring
  have hlk : 0 ≤ Real.log P.rd * F.kap := mul_nonneg hlrd0 hkap0
  have hPk : 0 ≤ P.PPp * F.kap := mul_nonneg hPPp0 hkap0
  have hQ2 : 2 * P.PPp * F.kap ≤ F.Q := by rw [hQe]; linarith only [hlk, hkap0]
  have hQ0 : 0 ≤ F.Q := by linarith only [hQ2, hPk]
  have hcflQ : |2 * F.cfl Cf| ≤ F.Q := by
    rw [hQe]; exact cfl_Q _ _ _ _ _ hEx (mul_nonneg hCf hL0) hCLk hlk
  have hGQ : 2 * Real.log (F.g : ℝ) ≤ F.Q := le_trans (g_Q _ _ _ _ hlogg hGP hkap hPPp0) hQ2
  have hmuNQ : |F.muN| ≤ F.Q := le_trans hMN hQ2
  have hmmQ : F.mmax ≤ F.Q := le_trans hLa hQ2
  obtain ⟨hdN, hdNs, hdb, hcut⟩ := cut_lines K (Fin F.nN → K) (Fin F.nN) (Pi.basisFun K (Fin F.nN)) F.XN hXN
    F.NN F.Mk F.e F.g hNfg hMkfg hN0 hg1 hee hsa hint hNM
  have hδQ : 12 * F.δ * F.Q = 24 * F.δ * ((P.PPp + 1 + Real.log P.rd) * F.kap) := by
    unfold SlopeBoundLiftData.Q SlopeBoundParameters.lrd; ring
  have hDF' : ∀ τ, |F.c1 τ + F.pq * P.logOm / 2| ≤ Cc * F.q' * (Real.log P.rd + |P.Lc|) := fun τ =>
    le_trans (hDF τ) (mul_le_mul_of_nonneg_left (by linarith [abs_nonneg P.Lc]) (mul_nonneg hCc hq0))
  have hB0 : 0 ≤ P.B0 := by
    unfold SlopeBoundParameters.B0
    have : 0 ≤ P.x ^ P.eps := Real.rpow_nonneg (by linarith) _
    have : 0 ≤ P.f * P.m * P.b := by positivity
    positivity
  have hBl : 0 ≤ P.B0 * P.llx := mul_nonneg hB0 (by linarith)
  have hBl' : P.B0 ≤ P.B0 * P.llx := by nlinarith only [hB0, hllx]
  have hdbQ : ((rkK F.bad : ℕ) : ℝ) ≤ 3 * F.δ * ((rkK F.NN : ℕ) : ℝ) := hBR
  have hcfl0 : F.cfl Cf = (∑ τ, F.w τ * F.c1 τ) - Cf * P.L := by
    unfold SlopeBoundLiftData.cfl; rw [hq]; ring
  have hfirst : -(2 * (C1 * P.LL0 * (∑ τ, F.ua τ) + P.b / 4)) ≤ F.muN - 2 * F.cfl Cf := by
    have hU' : F.U = ∑ τ, F.ua τ := rfl
    unfold LeafDef at hDe
    rw [hU'] at hDe
    rw [hcfl0]
    linarith only [hDe, hPPdef]
  have key := Formalism.ExtensionFiltration.covolume_assembly_weighted K d D hD hdD XWr hXWr M hM P.Pl F.w F.w0 F.c1 F.ua
    (F.muN - 2 * F.cfl Cf) F.muN F.muN F.muG F.mmax 1 1 (rkK F.NN : ℝ) (rkK F.good : ℝ) (rkK F.bad : ℝ)
    C1 Cf Cc (F.cfl Cf) 0 F.δ F.Q 0 0 (2 * Real.log (F.g : ℝ)) (2 * (F.o' + F.n2))
    F.pq F.q' P.logOm P.x P.eps P.L P.b P.rd |P.Lc| P.llx P.LL0 P.B0 P.f P.m P.k P.S P.η P.a P.La P.R 1
    hfirst rfl (by linarith only) one_pos le_rfl (by norm_num) le_rfl le_rfl (by linarith only) hcflQ hQ0
    (by linarith only [hb1])
    hdN hdNs hdb hdbQ hδ0 hδ12 hcut hmuNQ hmmQ hGQ hrec
    (by rw [hδQ]; linarith only [hδb, ho', hPPpp, hn2b, hb1])
    hDF' hwt hU hw hkS hkη hcard hm hf hq0 hq1 hx heps rfl rfl (by linarith only [hrd4]) hlrd (abs_nonneg _) hLc
    hlx hllx rfl rfl hC1 hCf hCc hsh hS hR hkR hk hpq rfl rfl le_rfl (by rw [one_mul]; exact hper)
  have hc : 64 * (C1 + 3 * Cf) + 8 * Cc + 2 + 12 * 1 + Cm ≤ slopeBoundConstant Ca Cb Cf Cc C1 Cm := by
    unfold slopeBoundConstant; linarith only [hCa, hCb]
  have hc' := mul_le_mul_of_nonneg_right hc hBl
  have hm' : Cm * P.B0 ≤ Cm * (P.B0 * P.llx) := mul_le_mul_of_nonneg_left hBl' hCm
  show Formalism.DivisionValues.lcv XW M / (D : ℝ) ≤ (∑ σ, F.pq * F.w0 σ * P.logOm) + slopeBoundConstant Ca Cb Cf Cc C1 Cm * (P.B0 * P.llx)
  have e1 : (64 * (C1 + 3 * Cf) + 8 * Cc + 2 + 12 * 1) * P.B0 * P.llx + Cm * (P.B0 * P.llx) =
      (64 * (C1 + 3 * Cf) + 8 * Cc + 2 + 12 * 1 + Cm) * (P.B0 * P.llx) := by ring
  linarith only [key, hmes, hc', hm', e1]

set_option maxHeartbeats 1000000 in

theorem slope_bound_single_lift_composed {K : Type} [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K]
    (Ca Cb Cf Cc C1 Cm Cn : ℝ) (hCa : 0 ≤ Ca) (hCb : 0 ≤ Cb) (hCf : 0 ≤ Cf) (hCc : 0 ≤ Cc) (hC1 : 0 ≤ C1)
    (hCm : 0 ≤ Cm) (d D : ℕ) (hD : 0 < D) (hdD : d = D) (XW XWr : InfinitePlace K → Matrix (Fin d) (Fin d) ℂ)
    (M : Submodule (𝓞 K) (Fin d → K)) (hM : Submodule.IsLattice K M) (P : SlopeBoundParameters) (F : SlopeBoundLiftData K P)
    (hKL : LeafKL P) (hCN : LeafCN P) (hFE : LeafFE P) (hDi : LeafDiff P) (hNo : LeafNorm P)
    (hPg : PageParams P) (hFa : FacParams Cf F) (hDF : LeafDegFlat Cc F) (hEx : LeafExport Cf F)
    (hCu : LeafCut F) (hSB : LeafShareBad F) (hBR : LeafBadRows F) (hMN : LeafMuN F) (hLa : LeafLam F)
    (hRe : LeafRecord XWr M F) (hN2 : LeafNote2 Cn F) (hMe : LeafMeasure Cm (D := D) XW XWr M P)
    (hc : LeafRoot F ∧ LeafFlat Cf F ∧ LeafDeg F ∧ LeafRho F ∧ LeafShare F ∧ LeafSmall F ∧
      LeafMeans Ca Cb F ∧ LeafHS F ∧ LeafSum F ∧ CrudeSizeBound F ∧ LeafEps F ∧ LeafDescent F ∧ LeafPh F ∧
      LeafGmin F ∧ CompParams Ca Cb F) :
    Formalism.DivisionValues.lcv XW M / (D : ℝ) ≤ F.main + slopeBoundConstant Ca Cb Cf Cc C1 Cm * (P.B0 * P.llx) := by
  obtain ⟨-, -, -, hx, heps, hrd4, hv2, hv, hlrd, hLc, hlx, hllx, hx7, hcard, hm, hf, hk, hkS, hkη, hS, hR, hkR,
    hGP, hPPpp, hPPdef⟩ := hPg
  obtain ⟨hwt, hU, hw, hsh, hpq, hq0, hq1, hkap, hCLk, hδb, hn2b⟩ := hFa
  obtain ⟨-, hper⟩ := period_of_leaves P hKL hCN hFE hDi hNo hv hv2 hrd4 hLc hx
  obtain ⟨hNfg, hMkfg, hN0, hXN, hg1, hee, hsa, hint, hNM, hlogg⟩ := hCu
  obtain ⟨hδ0, hδx⟩ := hSB
  obtain ⟨hXWr, hmes⟩ := hMe
  obtain ⟨hrec, ho'⟩ := hRe
  obtain ⟨hn20, -⟩ := hN2

  have hL0 : 0 ≤ P.L := Real.rpow_nonneg (by linarith) _
  have hb1 : 1 ≤ P.b := Real.one_le_exp hL0
  have hlrd0 : 0 ≤ Real.log P.rd := Real.log_nonneg (by linarith)
  have hδ12 : F.δ ≤ 1 / 12 := le_trans hδx (exp_neg_le_twelfth _ hx7)
  have hkap0 : 0 ≤ F.kap := by linarith
  have hfN : 0 ≤ 20 * P.f * P.Nr ^ 2 * P.L := by positivity
  have hPPp0 : 0 ≤ P.PPp := by linarith
  have hQe : F.Q = 2 * (P.PPp * F.kap) + 2 * F.kap + 2 * (Real.log P.rd * F.kap) := by
    unfold SlopeBoundLiftData.Q SlopeBoundParameters.lrd; ring
  have hlk : 0 ≤ Real.log P.rd * F.kap := mul_nonneg hlrd0 hkap0
  have hPk : 0 ≤ P.PPp * F.kap := mul_nonneg hPPp0 hkap0
  have hQ2 : 2 * P.PPp * F.kap ≤ F.Q := by rw [hQe]; linarith only [hlk, hkap0]
  have hQ0 : 0 ≤ F.Q := by linarith only [hQ2, hPk]
  have hcflQ : |2 * F.cfl Cf| ≤ F.Q := by
    rw [hQe]; exact cfl_Q _ _ _ _ _ hEx (mul_nonneg hCf hL0) hCLk hlk
  have hGQ : 2 * Real.log (F.g : ℝ) ≤ F.Q := le_trans (g_Q _ _ _ _ hlogg hGP hkap hPPp0) hQ2
  have hmuNQ : |F.muN| ≤ F.Q := le_trans hMN hQ2
  have hmmQ : F.mmax ≤ F.Q := le_trans hLa hQ2
  obtain ⟨hdN, hdNs, hdb, hcut⟩ := cut_lines K (Fin F.nN → K) (Fin F.nN) (Pi.basisFun K (Fin F.nN)) F.XN hXN
    F.NN F.Mk F.e F.g hNfg hMkfg hN0 hg1 hee hsa hint hNM
  have hδQ : 12 * F.δ * F.Q = 24 * F.δ * ((P.PPp + 1 + Real.log P.rd) * F.kap) := by
    unfold SlopeBoundLiftData.Q SlopeBoundParameters.lrd; ring
  have hDF' : ∀ τ, |F.c1 τ + F.pq * P.logOm / 2| ≤ Cc * F.q' * (Real.log P.rd + |P.Lc|) := fun τ =>
    le_trans (hDF τ) (mul_le_mul_of_nonneg_left (by linarith [abs_nonneg P.Lc]) (mul_nonneg hCc hq0))
  have hB0 : 0 ≤ P.B0 := by
    unfold SlopeBoundParameters.B0
    have : 0 ≤ P.x ^ P.eps := Real.rpow_nonneg (by linarith) _
    have : 0 ≤ P.f * P.m * P.b := by positivity
    positivity
  have hBl : 0 ≤ P.B0 * P.llx := mul_nonneg hB0 (by linarith)
  have hBl' : P.B0 ≤ P.B0 * P.llx := by nlinarith only [hB0, hllx]
  have hdbQ : ((rkK F.bad : ℕ) : ℝ) ≤ 3 * F.δ * ((rkK F.NN : ℕ) : ℝ) := hBR
  obtain ⟨⟨hmv0, hmv⟩, hFl, hDe, hρ0, hSh, ⟨hhcs, hcc, hV⟩, ⟨hX, hmean, hTX, hTcc⟩, ⟨hA, hR1, hR2, hHSc⟩, hSu,
    -, hEps, hDs, hPh, hGm, ⟨hDY, hT20, hDT, hDρ, hcs, hBn, hδ', hbud⟩⟩ := hc
  obtain ⟨hAfg, hBfg, -, hA0, -, hXA, hXB, hinj, hmap, hht, hPh0, hmuB, hminB, hrk, hεrk, hspan⟩ := hDs
  obtain ⟨hdA, hdAB, hdesc, -, -, -, -⟩ := descent_cut_lines K (Fin F.nA → K) (Fin F.nA) (Fin F.nB → K)
    (Fin F.nB) (Fin F.nN → K) (Fin F.nN) (Pi.basisFun K (Fin F.nA)) F.XA (Pi.basisFun K (Fin F.nB)) F.XB
    (Pi.basisFun K (Fin F.nN)) F.XN hXA hXB hXN F.φ F.LA F.LB F.NN F.Mk F.e F.g (2 * F.PPh) F.abelian₂
    hAfg hBfg hNfg hMkfg hA0 hN0 hinj hmap hht hmuB hminB hrk hspan hg1 hee hsa hint hNM
  have hT0 : 0 < F.T := by linarith only [hDY, hT20]
  have hρ1 : F.ρ < 1 := by nlinarith only [hDY, hDρ, hρ0]
  have hDT0 : 0 ≤ F.DY ^ 2 / F.T := div_nonneg (sq_nonneg _) hT0.le
  have hDρ0 : 0 ≤ F.DY * F.ρ := mul_nonneg (by linarith only [hDY]) hρ0
  have hz0 : 0 ≤ F.z := by unfold SlopeBoundLiftData.z; linarith only [hDT0, hDρ0]
  have hz1 : F.z < 1 := by unfold SlopeBoundLiftData.z; linarith only [hDT, hDρ]
  have hε0 : 0 ≤ F.ε := by
    unfold SlopeBoundLiftData.ε
    have : 0 ≤ 7 * F.DY ^ 2 / F.T := div_nonneg (by positivity) hT0.le
    linarith only [this, hDρ0]
  have hεQ : F.ε * F.Q ≤ P.b / 4 := by
    have : F.ε * F.Q = 2 * (F.ε * ((P.PPp + 1 + Real.log P.rd) * F.kap)) := by
      unfold SlopeBoundLiftData.Q SlopeBoundParameters.lrd; ring
    unfold LeafEps at hEps
    rw [this]; linarith only [hEps]
  have hTX' : F.T * F.X ≤ Ca * P.LL0 * (∑ τ, F.ua τ) + F.e1 Ca := by
    have : Ca * P.LL0 * (F.U + F.E0) = Ca * P.LL0 * (∑ τ, F.ua τ) + F.e1 Ca := by
      unfold SlopeBoundLiftData.e1 SlopeBoundLiftData.U; ring
    linarith only [hTX, this]
  have hTcc' : F.T * F.cc ≤ Cb * P.LL0 * (∑ τ, F.ua τ) + F.e2 Cb := by
    have : Cb * P.LL0 * (F.U + F.E0) + F.T * F.Qcc = Cb * P.LL0 * (∑ τ, F.ua τ) + F.e2 Cb := by
      unfold SlopeBoundLiftData.e2 SlopeBoundLiftData.U; ring
    linarith only [hTcc, this]
  have hbud' : F.cs * (6 * F.DY + 10 + F.T * (F.z + 2 * F.ρ)) + (F.A * Real.log (max F.A 1) + 4) + F.R1 +
      2 * F.z * F.R2 + (F.PPf + F.mv) + F.e1 Ca + F.e2 Cb ≤ P.b / 4 := by
    linarith only [hbud, hmv, hb1]
  have hsum' : 2 * ((∑ c, F.degc c) / (∑ c, F.dc c) - (F.PPf + F.mv)) ≤ F.muU - 2 * F.mv := by
    unfold LeafSum at hSu; linarith only [hSu]
  have hGm' : 2 * F.abelian₂ ≤ F.Q := by
    unfold LeafGmin at hGm; linarith only [hGm, hQ2]
  have hPh' : F.PPh ≤ P.PPpp := hPh
  have key := Formalism.ExtensionFiltration.covolume_full_assembly_weighted K d D hD hdD XWr hXWr M hM P.Pl F.w F.w0 F.c1 F.ua F.ι F.T F.DY F.A F.cs F.X
    F.cc F.z F.ρ F.R1 F.R2 F.Bn F.δ' F.h F.sl F.δc F.dc F.degc Ca Cb (F.PPf + F.mv) (F.e1 Ca) (F.e2 Cb)
    (F.muU - 2 * F.mv) F.muA F.muN F.muG F.mmax (rkK F.LA : ℝ) (rkK F.LB : ℝ) (rkK F.NN : ℝ)
    (rkK F.good : ℝ) (rkK F.bad : ℝ) Cf Cc (F.cfl Cf) F.ε F.δ F.Q (2 * F.PPh) (2 * F.abelian₂)
    (2 * Real.log (F.g : ℝ)) (2 * (F.o' + F.n2))
    F.pq F.q' P.logOm P.x P.eps P.L P.b P.rd |P.Lc| P.llx P.LL0 P.B0 P.f P.m P.k P.S P.η P.a P.La P.R 1
    (by linarith only [hDY]) (by linarith only [hDY, hT20]) hA hcs hX hcc hz0 hz1 hρ0 hρ1 hR1 hR2 hBn hδ' hDe hSh
    hhcs hV hmean hHSc hTX' hTcc' hbud' hsum' rfl hFl
    hdA hdAB hεrk hε0 (by linarith only [hPh0]) hdesc hcflQ hGm' hεQ
    hdN hdNs hdb hdbQ hδ0 hδ12 hcut hmuNQ hmmQ hGQ hrec
    (by rw [hδQ]; linarith only [hδb, ho', hPPpp, hn2b, hb1, hPh'])
    hDF' hwt hU hw hkS hkη hcard hm hf hq0 hq1 hx heps rfl rfl (by linarith only [hrd4]) hlrd (abs_nonneg _) hLc
    hlx hllx rfl rfl hCa hCb hCf hCc hsh hS hR hkR hk hpq rfl rfl le_rfl (by rw [one_mul]; exact hper)
  have hc : 64 * (Ca + Cb + 3 * Cf) + 8 * Cc + 2 + 12 * 1 + Cm ≤ slopeBoundConstant Ca Cb Cf Cc C1 Cm := by
    unfold slopeBoundConstant; linarith only [hC1]
  have hc' := mul_le_mul_of_nonneg_right hc hBl
  have hm' : Cm * P.B0 ≤ Cm * (P.B0 * P.llx) := mul_le_mul_of_nonneg_left hBl' hCm
  show Formalism.DivisionValues.lcv XW M / (D : ℝ) ≤ (∑ σ, F.pq * F.w0 σ * P.logOm) + slopeBoundConstant Ca Cb Cf Cc C1 Cm * (P.B0 * P.llx)
  have e1 : (64 * (Ca + Cb + 3 * Cf) + 8 * Cc + 2 + 12 * 1) * P.B0 * P.llx + Cm * (P.B0 * P.llx) =
      (64 * (Ca + Cb + 3 * Cf) + 8 * Cc + 2 + 12 * 1 + Cm) * (P.B0 * P.llx) := by ring
  linarith only [key, hmes, hc', hm', e1]

theorem slope_bound_single_lift {K : Type} [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K]
    (Ca Cb Cf Cc C1 Cm Cn : ℝ) (hCa : 0 ≤ Ca) (hCb : 0 ≤ Cb) (hCf : 0 ≤ Cf) (hCc : 0 ≤ Cc) (hC1 : 0 ≤ C1)
    (hCm : 0 ≤ Cm) (d D : ℕ) (hD : 0 < D) (hdD : d = D) (XW XWr : InfinitePlace K → Matrix (Fin d) (Fin d) ℂ)
    (M : Submodule (𝓞 K) (Fin d → K)) (hM : Submodule.IsLattice K M) (P : SlopeBoundParameters) (F : SlopeBoundLiftData K P)
    (hKL : LeafKL P) (hCN : LeafCN P) (hFE : LeafFE P) (hDi : LeafDiff P) (hNo : LeafNorm P)
    (hPg : PageParams P) (hFa : FacParams Cf F) (hDF : LeafDegFlat Cc F) (hEx : LeafExport Cf F)
    (hCu : LeafCut F) (hSB : LeafShareBad F) (hBR : LeafBadRows F) (hMN : LeafMuN F) (hLa : LeafLam F)
    (hRe : LeafRecord XWr M F) (hN2 : LeafNote2 Cn F) (hMe : LeafMeasure Cm (D := D) XW XWr M P)
    (hdef : F.q' = 0 → LeafDef C1 Cf F)
    (hcomp : F.q' ≠ 0 → LeafRoot F ∧ LeafFlat Cf F ∧ LeafDeg F ∧ LeafRho F ∧ LeafShare F ∧ LeafSmall F ∧
      LeafMeans Ca Cb F ∧ LeafHS F ∧ LeafSum F ∧ CrudeSizeBound F ∧ LeafEps F ∧ LeafDescent F ∧ LeafPh F ∧
      LeafGmin F ∧ CompParams Ca Cb F) :
    Formalism.DivisionValues.lcv XW M / (D : ℝ) ≤ F.main + slopeBoundConstant Ca Cb Cf Cc C1 Cm * (P.B0 * P.llx) := by
  by_cases hq : F.q' = 0
  · exact slope_bound_single_lift_of_definitions Ca Cb Cf Cc C1 Cm Cn hCa hCb hCf hCc hC1 hCm d D hD hdD XW XWr M hM P F hKL hCN hFE hDi hNo
      hPg hFa hDF hEx hCu hSB hBR hMN hLa hRe hN2 hMe hq (hdef hq)
  · exact slope_bound_single_lift_composed Ca Cb Cf Cc C1 Cm Cn hCa hCb hCf hCc hC1 hCm d D hD hdD XW XWr M hM P F hKL hCN hFE hDi hNo
      hPg hFa hDF hEx hCu hSB hBR hMN hLa hRe hN2 hMe (hcomp hq)

def ScaleTies {K : Type} [Field K] [NumberField K] [StarRing K] {Bs : DefBase K} (Zs : IndefScale Bs)
    (P : SlopeBoundParameters) (F : Bs.J → SlopeBoundLiftData K P) : Prop :=
  Zs.x = P.x ∧ Zs.b = P.b ∧ (Fintype.card Bs.J : ℝ) = P.m ∧ (∀ j, Zs.l3m j = (F j).main) ∧
    Zs.l3u = P.B0 * P.llx ∧ Function.Injective (fun j => (F j).q') ∧
    ∀ j, ((F j).q' : ℝ) + 1 ≤ P.m ∧ (F j).pq = P.k + P.m - 1 - 2 * ((F j).q' : ℝ)

theorem scaleTies_unique_def {K : Type} [Field K] [NumberField K] [StarRing K] {Bs : DefBase K} (Zs : IndefScale Bs)
    (P : SlopeBoundParameters) (F : Bs.J → SlopeBoundLiftData K P) (hT : ScaleTies Zs P F) (hm : 1 ≤ P.m) :
    ∃! j, (F j).q' = 0 := by
  obtain ⟨-, -, hcard, -, -, hinj, hq⟩ := hT
  have hlt : ∀ j, (F j).q' < Fintype.card Bs.J := by
    intro j
    have h1 := (hq j).1
    rw [← hcard] at h1
    exact_mod_cast (show ((F j).q' : ℝ) < (Fintype.card Bs.J : ℝ) by linarith)
  let g : Bs.J → Fin (Fintype.card Bs.J) := fun j => ⟨(F j).q', hlt j⟩
  have hg : Function.Injective g := fun a b h => hinj (show (F a).q' = (F b).q' from congrArg Fin.val h)
  have hbij : Function.Bijective g := (Fintype.bijective_iff_injective_and_card g).mpr ⟨hg, by simp⟩
  have hpos : 0 < Fintype.card Bs.J := by
    have : (1 : ℝ) ≤ Fintype.card Bs.J := by rw [hcard]; exact hm
    exact_mod_cast (show (0 : ℝ) < Fintype.card Bs.J by linarith)
  obtain ⟨j, hj⟩ := hbij.2 ⟨0, hpos⟩
  have hj0 : (F j).q' = 0 := congrArg Fin.val hj
  exact ⟨j, hj0, fun j' hj' => hinj (show (F j').q' = (F j).q' by rw [hj', hj0])⟩

theorem scaleTies_some_comp {K : Type} [Field K] [NumberField K] [StarRing K] {Bs : DefBase K} (Zs : IndefScale Bs)
    (P : SlopeBoundParameters) (F : Bs.J → SlopeBoundLiftData K P) (hT : ScaleTies Zs P F) (hm : 2 ≤ P.m) :
    ∃ j, (F j).q' ≠ 0 := by
  obtain ⟨-, -, hcard, -, -, hinj, -⟩ := hT
  have h2 : 1 < Fintype.card Bs.J := by
    have : (2 : ℝ) ≤ Fintype.card Bs.J := by rw [hcard]; exact hm
    exact_mod_cast (show (1 : ℝ) < Fintype.card Bs.J by linarith)
  obtain ⟨a, b, hab⟩ := Fintype.exists_pair_of_one_lt_card h2
  by_contra h
  simp only [ne_eq, not_exists, not_not] at h
  exact hab (hinj (show (F a).q' = (F b).q' by rw [h a, h b]))

theorem slope_bound_of_conditions {K : Type} [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K] {Bs : DefBase K}
    {Df : DefSide Bs} (Ca Cb Cf Cc C1 Cm Cn : ℝ) (hCa : 0 ≤ Ca) (hCb : 0 ≤ Cb) (hCf : 0 ≤ Cf) (hCc : 0 ≤ Cc)
    (hC1 : 0 ≤ C1) (hCm : 0 ≤ Cm) (S : IndefData Df) (Zs : IndefScale Bs) (CH : ℝ) (P : SlopeBoundParameters)
    (F : Bs.J → SlopeBoundLiftData K P) (XWr : ∀ j, InfinitePlace K → Matrix (Fin (S.dW j)) (Fin (S.dW j)) ℂ)
    (hKL : LeafKL P) (hCN : LeafCN P) (hFE : LeafFE P) (hDi : LeafDiff P) (hNo : LeafNorm P)
    (hPg : PageParams P) (hFa : ∀ j, FacParams Cf (F j)) (hDF : ∀ j, LeafDegFlat Cc (F j))
    (hEx : ∀ j, LeafExport Cf (F j)) (hCu : ∀ j, LeafCut (F j)) (hSB : ∀ j, LeafShareBad (F j))
    (hBR : ∀ j, LeafBadRows (F j)) (hMN : ∀ j, LeafMuN (F j)) (hLa : ∀ j, LeafLam (F j))
    (hRe : ∀ j, LeafRecord (XWr j) (S.M j) (F j)) (hN2 : ∀ j, LeafNote2 Cn (F j))
    (hMe : ∀ j, LeafMeasure Cm (D := S.D) (S.XW j) (XWr j) (S.M j) P)
    (hDef : ∀ j, (F j).q' = 0 → LeafDef C1 Cf (F j))
    (hRo : ∀ j, (F j).q' ≠ 0 → LeafRoot (F j)) (hFl : ∀ j, (F j).q' ≠ 0 → LeafFlat Cf (F j))
    (hDg : ∀ j, (F j).q' ≠ 0 → LeafDeg (F j)) (hRh : ∀ j, (F j).q' ≠ 0 → LeafRho (F j))
    (hSh : ∀ j, (F j).q' ≠ 0 → LeafShare (F j)) (hSm : ∀ j, (F j).q' ≠ 0 → LeafSmall (F j))
    (hMs : ∀ j, (F j).q' ≠ 0 → LeafMeans Ca Cb (F j)) (hHS : ∀ j, (F j).q' ≠ 0 → LeafHS (F j))
    (hSu : ∀ j, (F j).q' ≠ 0 → LeafSum (F j)) (hI13 : ∀ j, (F j).q' ≠ 0 → CrudeSizeBound (F j))
    (hEp : ∀ j, (F j).q' ≠ 0 → LeafEps (F j)) (hDs : ∀ j, (F j).q' ≠ 0 → LeafDescent (F j))
    (hPh : ∀ j, (F j).q' ≠ 0 → LeafPh (F j)) (hGm : ∀ j, (F j).q' ≠ 0 → LeafGmin (F j))
    (hCP : ∀ j, (F j).q' ≠ 0 → CompParams Ca Cb (F j))
    (hD : 0 < S.D) (hdW : ∀ j, S.dW j = S.D) (hF : S.Frames) (hT : ScaleTies Zs P F) :
    S.L3 (Zs.num (slopeBoundConstant Ca Cb Cf Cc C1 Cm) CH) := by
  obtain ⟨-, -, -, hmain, hunit, -⟩ := hT
  intro j
  have key := slope_bound_single_lift Ca Cb Cf Cc C1 Cm Cn hCa hCb hCf hCc hC1 hCm (S.dW j) S.D hD (hdW j) (S.XW j) (XWr j)
    (S.M j) (hF.2.2 j) P (F j) hKL hCN hFE hDi hNo hPg (hFa j) (hDF j) (hEx j) (hCu j) (hSB j) (hBR j) (hMN j)
    (hLa j) (hRe j) (hN2 j) (hMe j) (hDef j)
    (fun hq => ⟨hRo j hq, hFl j hq, hDg j hq, hRh j hq, hSh j hq, hSm j hq, hMs j hq, hHS j hq, hSu j hq,
      hI13 j hq, hEp j hq, hDs j hq, hPh j hq, hGm j hq, hCP j hq⟩)
  show Formalism.DivisionValues.lcv (S.XW j) (S.M j) / (S.D : ℝ) ≤ Zs.l3m j + slopeBoundConstant Ca Cb Cf Cc C1 Cm * Zs.l3u
  rw [hmain j, hunit]
  exact key

theorem slope_bound_of_conditions_for_frames {K : Type} [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K] {Bs : DefBase K}
    {Df : DefSide Bs} (Ca Cb Cf Cc C1 Cm Cn : ℝ) (hCa : 0 ≤ Ca) (hCb : 0 ≤ Cb) (hCf : 0 ≤ Cf) (hCc : 0 ≤ Cc)
    (hC1 : 0 ≤ C1) (hCm : 0 ≤ Cm) (S : IndefRows Df) (wf : Df.WF) (Zs : IndefScale Bs) (CH : ℝ) (P : SlopeBoundParameters)
    (F : Bs.J → SlopeBoundLiftData K P)
    (XWr : ∀ j, InfinitePlace K → Matrix (Fin (S.toIndefData.dW j)) (Fin (S.toIndefData.dW j)) ℂ)
    (hKL : LeafKL P) (hCN : LeafCN P) (hFE : LeafFE P) (hDi : LeafDiff P) (hNo : LeafNorm P)
    (hPg : PageParams P) (hFa : ∀ j, FacParams Cf (F j)) (hDF : ∀ j, LeafDegFlat Cc (F j))
    (hEx : ∀ j, LeafExport Cf (F j)) (hCu : ∀ j, LeafCut (F j)) (hSB : ∀ j, LeafShareBad (F j))
    (hBR : ∀ j, LeafBadRows (F j)) (hMN : ∀ j, LeafMuN (F j)) (hLa : ∀ j, LeafLam (F j))
    (hRe : ∀ j, LeafRecord (XWr j) (S.toIndefData.M j) (F j)) (hN2 : ∀ j, LeafNote2 Cn (F j))
    (hMe : ∀ j, LeafMeasure Cm (D := S.toIndefData.D) (S.toIndefData.XW j) (XWr j) (S.toIndefData.M j) P)
    (hDef : ∀ j, (F j).q' = 0 → LeafDef C1 Cf (F j))
    (hRo : ∀ j, (F j).q' ≠ 0 → LeafRoot (F j)) (hFl : ∀ j, (F j).q' ≠ 0 → LeafFlat Cf (F j))
    (hDg : ∀ j, (F j).q' ≠ 0 → LeafDeg (F j)) (hRh : ∀ j, (F j).q' ≠ 0 → LeafRho (F j))
    (hSh : ∀ j, (F j).q' ≠ 0 → LeafShare (F j)) (hSm : ∀ j, (F j).q' ≠ 0 → LeafSmall (F j))
    (hMs : ∀ j, (F j).q' ≠ 0 → LeafMeans Ca Cb (F j)) (hHS : ∀ j, (F j).q' ≠ 0 → LeafHS (F j))
    (hSu : ∀ j, (F j).q' ≠ 0 → LeafSum (F j)) (hI13 : ∀ j, (F j).q' ≠ 0 → CrudeSizeBound (F j))
    (hEp : ∀ j, (F j).q' ≠ 0 → LeafEps (F j)) (hDs : ∀ j, (F j).q' ≠ 0 → LeafDescent (F j))
    (hPh : ∀ j, (F j).q' ≠ 0 → LeafPh (F j)) (hGm : ∀ j, (F j).q' ≠ 0 → LeafGmin (F j))
    (hCP : ∀ j, (F j).q' ≠ 0 → CompParams Ca Cb (F j)) (hT : ScaleTies Zs P F) :
    S.toIndefData.L3 (Zs.num (slopeBoundConstant Ca Cb Cf Cc C1 Cm) CH) :=
  slope_bound_of_conditions Ca Cb Cf Cc C1 Cm Cn hCa hCb hCf hCc hC1 hCm S.toIndefData Zs CH P F XWr hKL hCN hFE hDi hNo hPg
    hFa hDF hEx hCu hSB hBR hMN hLa hRe hN2 hMe hDef hRo hFl hDg hRh hSh hSm hMs hHS hSu hI13 hEp hDs hPh hGm hCP
    (IndefRows.D_pos S) (fun j => IndefRows.dW_eq S wf j) S.frames hT

def PeriodIdentity (n : ℕ) [NeZero n] (χ : DirichletCharacter ℂ n) : Prop :=
  ∃ Zv : ℝ, Zv = Real.log (2 / Real.sqrt (n : ℝ)) + (eulerConstantTerm n + Real.log Real.pi) ∧
    Zv = Real.log (2 * Real.pi) + leadingConstant χ ∧
    leadingConstant χ = -LcOf χ - Real.log ((n : ℝ) / Real.pi) + Real.eulerMascheroniConstant + Real.log 2

theorem leaves_satisfiable {K : Type} [Field K] [NumberField K] [StarRing K] {d D : ℕ}
    (XW : InfinitePlace K → Matrix (Fin d) (Fin d) ℂ) (M : Submodule (𝓞 K) (Fin d → K))
    (hXW : ∀ v, IsUnit (XW v).det) (hMfg : M.FG) (hM0 : M ≠ ⊥)
    (n : ℕ) [NeZero n] (χ : DirichletCharacter ℂ n)
    (hχ : (∀ k : ℕ, χ k = ((jacobiSym k n : ℤ) : ℂ)) ∧ χ.IsPrimitive ∧ χ.Odd) (hper : PeriodIdentity n χ) :
    ∃ (P : SlopeBoundParameters) (F : SlopeBoundLiftData K P), LeafKL P ∧ LeafCN P ∧ LeafFE P ∧ LeafDiff P ∧ LeafNorm P ∧
      PageParams P ∧ FacParams 0 F ∧ LeafDegFlat 0 F ∧ LeafExport 0 F ∧ LeafCut F ∧ LeafShareBad F ∧
      LeafBadRows F ∧ LeafMuN F ∧ LeafLam F ∧ LeafRecord XW M F ∧ LeafNote2 0 F ∧
      LeafMeasure 0 (D := D) XW XW M P ∧ F.q' = 0 ∧ LeafDef 0 0 F ∧ P.m = 1 ∧
      F.pq = P.k + P.m - 1 - 2 * (F.q' : ℝ) := by
  obtain ⟨Zv, hKL, hCN, hFE⟩ := hper
  obtain ⟨μ, hμ⟩ : ∃ t : ℝ, t = muDef (Pi.basisFun K (Fin d)) XW M := ⟨_, rfl⟩
  obtain ⟨μx, hμx⟩ : ∃ t : ℝ, t = muMaxDef (Pi.basisFun K (Fin d)) XW M := ⟨_, rfl⟩
  obtain ⟨E, hE⟩ : ∃ t : ℝ, t = 13 + |LcOf χ| + |μ| := ⟨_, rfl⟩
  obtain ⟨x0, hx0⟩ : ∃ t : ℝ, t = Real.exp (Real.exp E) := ⟨_, rfl⟩
  have hE13 : 13 ≤ E := by rw [hE]; linarith [abs_nonneg (LcOf χ), abs_nonneg μ]
  have hexpE : E + 1 ≤ Real.exp E := Real.add_one_le_exp E
  have hx0E : Real.exp E + 1 ≤ x0 := by rw [hx0]; exact Real.add_one_le_exp _
  have hlx0 : Real.log x0 = Real.exp E := by rw [hx0, Real.log_exp]
  have hllx0 : Real.log (Real.log x0) = E := by rw [hlx0, Real.log_exp]
  have hx0pos : 0 < x0 := by rw [hx0]; exact Real.exp_pos _
  have hx14 : 14 ≤ x0 := by linarith
  have hL : x0 ^ (1 : ℝ) = x0 := Real.rpow_one x0
  have hb4 : 4 * |μ| ≤ Real.exp x0 := by
    have hq := Real.quadratic_le_exp_of_nonneg (show (0 : ℝ) ≤ x0 by linarith)
    have hxμ : |μ| + 14 ≤ x0 := by linarith [abs_nonneg (LcOf χ)]
    nlinarith [abs_nonneg μ]
  have hbpos : 0 < Real.exp x0 := Real.exp_pos _
  have hb1 : 1 ≤ Real.exp x0 := Real.one_le_exp (by linarith)
  have hx7 : 3 ≤ x0 ^ ((1 : ℝ) / 7) := by
    rw [Real.rpow_def_of_pos hx0pos, hlx0]
    have h2 : 2 ≤ Real.exp E * (1 / 7) := by linarith
    have h3 : (3 : ℝ) ≤ Real.exp 2 := by linarith [Real.add_one_le_exp (2 : ℝ)]
    exact le_trans h3 (Real.exp_le_exp.mpr h2)
  have hl4 : Real.log 4 ≤ 3 := by
    have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 4 by norm_num); linarith
  have hcut : M ⊓ (LinearMap.range (LinearMap.id : (Fin d → K) →ₗ[K] (Fin d → K))).restrictScalars (𝓞 K) = M := by
    rw [LinearMap.range_id, Submodule.restrictScalars_top, inf_top_eq]
  have hbad : M ⊓ (LinearMap.ker (LinearMap.id : (Fin d → K) →ₗ[K] (Fin d → K))).restrictScalars (𝓞 K) = ⊥ := by
    rw [LinearMap.ker_id, Submodule.restrictScalars_bot, inf_bot_eq]
  have hrk0 : rkK (⊥ : Submodule (𝓞 K) (Fin d → K)) = 0 := by
    unfold rkK; simp
  let P : SlopeBoundParameters :=
    { Pl := Unit, fPl := inferInstance, x := x0, eps := 1, rd := 4, v := 2, dN := n, dimNeZero := inferInstance, χ := χ,
      Z := Zv, logOmK := eulerConstantTerm n, logOm := eulerConstantTerm n - Real.log 4 + Real.log (Real.sqrt (n : ℝ)), f := 1, m := 1,
      k := 1, S := 1, η := 0, R := 0, PPp := 1, PPpp := 0, PP := |μ|, PPT := 0, Zpg := 0, nV := 0, Nr := 0,
      g12 := 1 }
  have hPL : P.L = x0 := hL
  have hPb : P.b = Real.exp x0 := by show Real.exp P.L = _; rw [hPL]
  let F : SlopeBoundLiftData K P :=
    { w := fun _ => 0, w0 := fun _ => 0, c1 := fun _ => -(P.logOm / 2), ua := fun _ => 1, kap := |μ| + |μx| + 1,
      q' := 0, pq := 1, ι := Unit, fι := inferInstance, nι := inferInstance, DY := 0, A := 1, cs := 0, X := 0,
      cc := 0, E0 := 0, Qcc := 0, ρ := 0, R1 := 0, R2 := 0, Bn := 1, δ' := 1, h := fun _ => 0,
      sl := fun _ => 0, δc := fun _ => 1, dc := fun _ => 1, degc := fun _ => 0, PPf := 0, mv := 0, muU := 0,
      nA := d, nB := d, nN := d, XA := XW, XB := XW, XN := XW, LA := M, LB := M, NN := M, Mk := M,
      φ := LinearMap.id, e := LinearMap.id, g := 1, PPh := 0, abelian₂ := 0, δ := 0, o' := 0, n2 := 0 }
  have hU : F.U = 1 := by show (∑ _τ : Unit, (1 : ℝ)) = 1; simp
  have hμ0 := abs_nonneg μ
  have hμx0 := abs_nonneg μx
  refine ⟨P, F, hKL, hCN, hFE, rfl, rfl, ?_, ?_, ?_, ?_, ?_, ⟨le_rfl, (Real.exp_pos _).le⟩, ?_, ?_, ?_, ?_, ?_, ?_,
    rfl, ?_, rfl, ?_⟩
  ·
    refine ⟨hχ.1, hχ.2.1, hχ.2.2, ?_, one_pos, le_rfl, by norm_num, by norm_num, ?_, ?_, ?_, ?_, ?_, ?_, le_rfl,
      le_rfl, le_rfl, ?_, ?_, zero_le_one, le_rfl, ?_, ?_, ?_, ?_⟩
    · show 1 ≤ x0; linarith
    · show Real.log 4 ≤ P.L; rw [hPL]; linarith
    · show |LcOf χ| ≤ P.L; rw [hPL]; linarith [abs_nonneg μ]
    · show Real.log x0 ≤ P.L; rw [hPL, hlx0]; linarith
    · show 1 ≤ Real.log (Real.log x0); rw [hllx0]; linarith
    · show 3 ≤ x0 ^ ((1 : ℝ) / 7); exact hx7
    · show ((Fintype.card Unit : ℕ) : ℝ) ≤ 1; simp
    · show (1 : ℝ) * 1 ≤ P.b; rw [hPb]; linarith
    · show (1 : ℝ) * 0 ≤ P.b; rw [hPb]; linarith
    · show (1 : ℝ) * 0 ≤ P.b; rw [hPb]; linarith
    · show 20 * (1 : ℝ) * 0 ^ 2 * P.L ≤ 1; simp
    · show (0 : ℝ) ≤ P.b / 8; rw [hPb]; positivity
    · show |μ| + 2 * 0 * 0 ≤ P.b / 4; rw [hPb]; linarith
  ·
    refine ⟨fun _ => ⟨by norm_num, by norm_num⟩, by rw [hU], fun _ => ⟨le_rfl, ?_⟩, fun _ => by show |(0 : ℝ) - 0| ≤ 1 + 0; norm_num,
      by show |(1 : ℝ) - 1| ≤ 1; norm_num,
      Nat.cast_nonneg _, by show ((0 : ℕ) : ℝ) ≤ 1; norm_num, by show (1 : ℝ) ≤ |μ| + |μx| + 1; linarith, by show 0 * P.L ≤ |μ| + |μx| + 1; simp; linarith,
      by show 24 * (0 : ℝ) * _ ≤ P.b / 8; rw [hPb]; simp; positivity, by show 2 * (0 : ℝ) ≤ P.b / 8; rw [hPb]; simp; positivity⟩
    show (0 : ℝ) ≤ 2 * P.b; rw [hPb]; positivity
  · intro _
    show |-(P.logOm / 2) + 1 * P.logOm / 2| ≤ 0 * ((0 : ℕ) : ℝ) * Real.log 4
    rw [show -(P.logOm / 2) + 1 * P.logOm / 2 = 0 by ring]; simp
  · show |(∑ _τ : Unit, (0 : ℝ) * -(P.logOm / 2)) - 0 * ((0 : ℕ) : ℝ) * Real.log 4 * (∑ _τ : Unit, (0 : ℝ))| ≤
      1 * (|μ| + |μx| + 1)
    simp; linarith
  · refine ⟨hMfg, hMfg, hM0, hXW, le_rfl, LinearMap.id_comp _, fun _ _ _ => rfl, fun y hy => ?_, le_rfl, ?_⟩
    · show (((1 : ℕ) : ℕ) : K) • (LinearMap.id : (Fin d → K) →ₗ[K] (Fin d → K)) y ∈ M
      simpa using hy
    · show Real.log ((1 : ℕ) : ℝ) ≤ 20 * 1 * 0 ^ 2 * P.L; simp
  · show ((rkK (M ⊓ (LinearMap.ker (LinearMap.id : (Fin d → K) →ₗ[K] (Fin d → K))).restrictScalars (𝓞 K)) : ℕ) : ℝ)
      ≤ 3 * 0 * ((rkK M : ℕ) : ℝ)
    rw [hbad, hrk0]; simp
  · show |muDef (Pi.basisFun K (Fin d)) XW M| ≤ 2 * 1 * (|μ| + |μx| + 1); rw [← hμ]; linarith
  · show muMaxDef (Pi.basisFun K (Fin d)) XW M ≤ 2 * 1 * (|μ| + |μx| + 1); rw [← hμx]; linarith [le_abs_self μx]
  · refine ⟨?_, le_rfl⟩
    show muDef (Pi.basisFun K (Fin d)) XW
        (M ⊓ (LinearMap.range (LinearMap.id : (Fin d → K) →ₗ[K] (Fin d → K))).restrictScalars (𝓞 K)) - 2 * (0 + 0)
      ≤ muDef (Pi.basisFun K (Fin d)) XW M
    rw [hcut]; linarith
  · refine ⟨le_rfl, ?_⟩; show (0 : ℝ) ≤ 0 * 1 * 0 ^ 2 * Real.log (0 * 4 * 1); simp
  · exact ⟨hXW, by simp⟩
  · show (∑ _τ : Unit, (0 : ℝ) * -(P.logOm / 2)) - 0 * P.LL0 * F.U - |μ| - (2 * 0 * 0 + 0 * P.L)
      ≤ muDef (Pi.basisFun K (Fin d)) XW M / 2
    rw [← hμ]; simp
    have := neg_abs_le μ; linarith
  · show (1 : ℝ) = 1 + 1 - 1 - 2 * ((0 : ℕ) : ℝ); norm_num

theorem exampleSingleLift_ne_bot : Examples₂.sl Examples₂.K3 1 ≠ ⊥ := by
  intro h
  have hm : Examples₂.sb Examples₂.K3 1 0 ∈ Examples₂.sl Examples₂.K3 1 := Submodule.subset_span ⟨0, rfl⟩
  rw [h, Submodule.mem_bot] at hm
  have := congrFun hm 0
  simp [Examples₂.sb] at this

theorem example_exists_slopeBound_conditions_of_jacobiSym (v0 : InfinitePlace Examples₂.K3) (n : ℕ) [NeZero n] (χ : DirichletCharacter ℂ n)
    (hχ : (∀ k : ℕ, χ k = ((jacobiSym k n : ℤ) : ℂ)) ∧ χ.IsPrimitive ∧ χ.Odd) (hper : PeriodIdentity n χ) :
    ∃ (P : SlopeBoundParameters) (F : (Examples₂.one.base Examples₂.K3 v0).J → SlopeBoundLiftData Examples₂.K3 P)
      (Zs : IndefScale (Examples₂.one.base Examples₂.K3 v0)),
      LeafKL P ∧ LeafCN P ∧ LeafFE P ∧ LeafDiff P ∧ LeafNorm P ∧ PageParams P ∧
      (∀ j, FacParams 0 (F j) ∧ LeafDegFlat 0 (F j) ∧ LeafExport 0 (F j) ∧ LeafCut (F j) ∧ LeafShareBad (F j) ∧
        LeafBadRows (F j) ∧ LeafMuN (F j) ∧ LeafLam (F j) ∧
        LeafRecord ((Examples₂.one.dat Examples₂.K3 v0).XW j) ((Examples₂.one.dat Examples₂.K3 v0).M j) (F j) ∧ LeafNote2 0 (F j) ∧
        LeafMeasure 0 (D := (Examples₂.one.dat Examples₂.K3 v0).D) ((Examples₂.one.dat Examples₂.K3 v0).XW j)
          ((Examples₂.one.dat Examples₂.K3 v0).XW j) ((Examples₂.one.dat Examples₂.K3 v0).M j) P ∧
        (F j).q' = 0 ∧ LeafDef 0 0 (F j)) ∧
      ScaleTies Zs P F := by
  have hfr := Examples₂.one.frames Examples₂.K3 v0
  obtain ⟨P, F, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21⟩ :=
    leaves_satisfiable (D := (Examples₂.one.dat Examples₂.K3 v0).D) ((Examples₂.one.dat Examples₂.K3 v0).XW ())
      ((Examples₂.one.dat Examples₂.K3 v0).M ()) (hfr.2.1 ()) (hfr.2.2 ()).fg exampleSingleLift_ne_bot n χ hχ hper
  refine ⟨P, fun _ => F,
    { F0 := fun _ _ => 0, J0 := fun _ _ _ => 0, E1u := 0, l3m := fun _ => F.main, l3u := P.B0 * P.llx,
      l6m := fun _ => 0, l6u := 0, x := P.x, b := P.b, la := 0, de := 0 },
    h1, h2, h3, h4, h5, h6, fun _ => ⟨h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19⟩,
    rfl, rfl, ?_, fun _ => rfl, rfl, ?_, fun _ => ⟨?_, h21⟩⟩
  · show ((Fintype.card Unit : ℕ) : ℝ) = P.m
    rw [h20]; simp
  · intro a b _
    exact Subsingleton.elim (α := Unit) a b
  · show ((F.q' : ℕ) : ℝ) + 1 ≤ P.m
    rw [h18, h20]; simp

theorem example_slope_bound_nontrivial (v0 : InfinitePlace Examples₂.K3) :
    ∃ N : IndefNum (Examples₂.one.base Examples₂.K3 v0), ¬ (Examples₂.one.dat Examples₂.K3 v0).L3 N := by
  refine ⟨{ Examples₂.one.num Examples₂.K3 v0 with
    l3 := fun _ => Formalism.DivisionValues.lcv (Examples₂.fr Examples₂.K3 1) (Examples₂.sl Examples₂.K3 1) / ((1 : ℕ) : ℝ) - 1 }, fun h => ?_⟩
  have := h ()
  change Formalism.DivisionValues.lcv (Examples₂.fr Examples₂.K3 1) (Examples₂.sl Examples₂.K3 1) / ((1 : ℕ) : ℝ) ≤
    Formalism.DivisionValues.lcv (Examples₂.fr Examples₂.K3 1) (Examples₂.sl Examples₂.K3 1) / ((1 : ℕ) : ℝ) - 1 at this
  linarith

end Formalism.L2.Indef.Tree
