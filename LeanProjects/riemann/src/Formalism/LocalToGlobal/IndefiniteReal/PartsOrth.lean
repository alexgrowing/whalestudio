import Mathlib
import Formalism.LocalToGlobal.IndefiniteForms.IndefSide
import Formalism.LocalToGlobal.Divisibility.RowLat

open Module NumberField IsDedekindDomain
open scoped Matrix ComplexOrder InnerProductSpace

noncomputable section

namespace Formalism.IndefR.Cx

open Formalism.DivisionValues Formalism.L2.Indef Formalism.L2.DIV

variable {K : Type} [Field K] [NumberField K] [StarRing K]

section SlopeTestRemainingChoices

def cpt (σ : K →+* ℂ) {n : ℕ} (x : Fin n → K) : Fin n → ℂ := fun i => σ (x i)

def cptL (σ : K →+* ℂ) (n : ℕ) : (Fin n → K) →ₛₗ[σ] (Fin n → ℂ) where
  toFun := cpt σ
  map_add' x y := by funext i; simp [cpt]
  map_smul' a x := by funext i; simp [cpt]

open Classical in

def kOf (σ : K →+* ℂ) (z : ℂ) : K := if h : ∃ a : K, σ a = z then h.choose else 0

def kMat (σ : K →+* ℂ) {m n : ℕ} (M : Matrix (Fin m) (Fin n) ℂ) : Matrix (Fin m) (Fin n) K := M.map (kOf σ)

def IsRat (σ : K →+* ℂ) {m n : ℕ} (M : Matrix (Fin m) (Fin n) ℂ) : Prop := ∀ i k, ∃ a : K, σ a = M i k

def lin {E : Type} [AddCommGroup E] [Module ℂ E] {n : ℕ} (v : Fin n → E) : (Fin n → ℂ) →ₗ[ℂ] E :=
  Fintype.linearCombination ℂ v

open Classical in

def solve {E : Type} [AddCommGroup E] [Module ℂ E] {n : ℕ} (f : (Fin n → ℂ) →ₗ[ℂ] E) (e : E) : Fin n → ℂ :=
  if h : ∃ y, f y = e then h.choose else 0

def relMat {E : Type} [AddCommGroup E] [Module ℂ E] {D n : ℕ} (f : (Fin D → ℂ) →ₗ[ℂ] E) (g : (Fin n → ℂ) →ₗ[ℂ] E) :
    Matrix (Fin D) (Fin n) ℂ :=
  Matrix.of fun i k => solve f (g (Pi.single k 1)) i

end SlopeTestRemainingChoices

def lv {Bs : DefBase K} (f : DefFace Bs) (b : Bool) : DefSide Bs := cond b f.Df1 f.Df0

structure Crd {Bs : DefBase K} (A : DefAmb Bs) (fc : DefSub A → DefFace Bs) where

  toR : ∀ Zs b t, (Fin ((lv (fc Zs) b).dQ t) → K) →ₗ[K] A.FR t

  toL : ∀ Zs b j t, (Fin ((lv (fc Zs) b).dZ j t) → K) →ₗ[K] A.FL j t

structure CxData {Bs : DefBase K} (A : DefAmb Bs) where

  FC : Bs.Tup → Type
  [nFC : ∀ t, NormedAddCommGroup (FC t)]
  [iFC : ∀ t, InnerProductSpace ℂ (FC t)]
  [dFC : ∀ t, FiniteDimensional ℂ (FC t)]

  jR : ∀ t, A.FR t →ₛₗ[Bs.v0.embedding] FC t

  EE : Type
  [nEE : NormedAddCommGroup EE]
  [iEE : InnerProductSpace ℂ EE]
  [dEE : FiniteDimensional ℂ EE]

  Θ : ∀ t, FC t →ₗ[ℂ] EE

  EEp : Bs.Ix → Submodule ℂ EE

  EEl : Bool → Submodule ℂ EE

  FLC : Bs.J → Bs.Tup → Type
  [nFLC : ∀ j t, NormedAddCommGroup (FLC j t)]
  [iFLC : ∀ j t, InnerProductSpace ℂ (FLC j t)]
  [dFLC : ∀ j t, FiniteDimensional ℂ (FLC j t)]

  jL : ∀ j t, A.FL j t →ₛₗ[Bs.v0.embedding] FLC j t

  W : Bs.J → Type
  [nW : ∀ j, NormedAddCommGroup (W j)]
  [iW : ∀ j, InnerProductSpace ℂ (W j)]
  [fW : ∀ j, FiniteDimensional ℂ (W j)]

  θ' : ∀ j t, FLC j t →ₗ[ℂ] W j

  Wp : ∀ j, Bs.Ix → Submodule ℂ (W j)

  dW : Bool → Bs.J → ℕ

  WC : Bool → Bs.J → InfinitePlace K → Type
  [nWC : ∀ b j v, NormedAddCommGroup (WC b j v)]
  [iWC : ∀ b j v, InnerProductSpace ℂ (WC b j v)]

  bW : ∀ b j v, Fin (dW b j) → WC b j v

  eW : ∀ b j, WC b j Bs.v0 →ₗ[ℂ] W j

  M : ∀ b j, Submodule (𝓞 K) (Fin (dW b j) → K)

  nP : Bool → ℝ

  μ : HeightOneSpectrum (𝓞 K) → Bs.Tup

  Tw : Finset (HeightOneSpectrum (𝓞 K))

  κ : InfinitePlace K → ℝ

  lam : Bs.J → Bs.Tup → Bs.Ix → InfinitePlace K → ℝ

  err0 : HeightOneSpectrum (𝓞 K) → Bs.J → ℝ

attribute [instance] CxData.nFC CxData.iFC CxData.dFC CxData.nEE CxData.iEE CxData.dEE CxData.nFLC CxData.iFLC CxData.dFLC
  CxData.nW CxData.iW CxData.fW CxData.nWC CxData.iWC

namespace CxData

variable {Bs : DefBase K} {A : DefAmb Bs} (X : CxData A)

def Z (t : Bs.Tup) : Submodule K (A.FR t) :=
  (LinearMap.range (LinearMap.adjoint (X.Θ t))).comap (X.jR t)

def Zl (j : Bs.J) (t : Bs.Tup) : Submodule K (A.FL j t) :=
  (LinearMap.range (LinearMap.adjoint (X.θ' j t))).comap (X.jL j t)

def zs : DefSub A := ⟨X.Z, X.Zl⟩

section Level

variable {fc : DefSub A → DefFace Bs} (cr : Crd A fc) (b : Bool)

def iC (t : Bs.Tup) : (Fin ((lv (fc X.zs) b).dQ t) → ℂ) →ₗ[ℂ] X.EE :=
  lin fun k => X.Θ t (X.jR t (cr.toR X.zs b t (Pi.single k 1)))

def rowMatC (t : Bs.Tup) : Matrix (Fin ((lv (fc X.zs) b).dQ Bs.μ0)) (Fin ((lv (fc X.zs) b).dQ t)) ℂ :=
  relMat (X.iC cr b Bs.μ0) (X.iC cr b t)

def rowMat (t : Bs.Tup) : Matrix (Fin ((lv (fc X.zs) b).dQ Bs.μ0)) (Fin ((lv (fc X.zs) b).dQ t)) K :=
  kMat Bs.v0.embedding (X.rowMatC cr b t)

def gramE : Matrix (Fin ((lv (fc X.zs) b).dQ Bs.μ0)) (Fin ((lv (fc X.zs) b).dQ Bs.μ0)) ℂ :=
  (((X.nP b)⁻¹ : ℝ) : ℂ) • Matrix.gram ℂ fun i => X.iC cr b Bs.μ0 (Pi.single i 1)

def XE : InfinitePlace K → Matrix (Fin ((lv (fc X.zs) b).dQ Bs.μ0)) (Fin ((lv (fc X.zs) b).dQ Bs.μ0)) ℂ :=
  rowXE (lv (fc X.zs) b) (frameOf (X.gramE cr b)) X.κ (fun j p v => X.lam j Bs.μ0 p v)

def Ep (p : Bs.Ix) : Submodule K (Fin ((lv (fc X.zs) b).dQ Bs.μ0) → K) :=
  (X.EEp p).comap ((X.iC cr b Bs.μ0).comp (cptL Bs.v0.embedding _))

def tC (j : Bs.J) (t : Bs.Tup) : (Fin ((lv (fc X.zs) b).dZ j t) → ℂ) →ₗ[ℂ] X.W j :=
  lin fun k => X.θ' j t (X.jL j t (cr.toL X.zs b j t (Pi.single k 1)))

def wC (j : Bs.J) (v : InfinitePlace K) : (Fin (X.dW b j) → ℂ) →ₗ[ℂ] X.WC b j v := lin (X.bW b j v)

def w0C (j : Bs.J) : (Fin (X.dW b j) → ℂ) →ₗ[ℂ] X.W j := (X.eW b j).comp (X.wC b j Bs.v0)

def liftMatC (j : Bs.J) (t : Bs.Tup) : Matrix (Fin (X.dW b j)) (Fin ((lv (fc X.zs) b).dZ j t)) ℂ :=
  relMat (X.w0C b j) (X.tC cr b j t)

def liftMat (j : Bs.J) (t : Bs.Tup) : Matrix (Fin (X.dW b j)) (Fin ((lv (fc X.zs) b).dZ j t)) K :=
  kMat Bs.v0.embedding (X.liftMatC cr b j t)

def XW (j : Bs.J) : InfinitePlace K → Matrix (Fin (X.dW b j)) (Fin (X.dW b j)) ℂ :=
  fun v => frameOf (Matrix.gram ℂ (X.bW b j v))

def WpK (j : Bs.J) (p : Bs.Ix) : Submodule K (Fin (X.dW b j) → K) :=
  (X.Wp j p).comap ((X.w0C b j).comp (cptL Bs.v0.embedding _))

def data : IndefData (lv (fc X.zs) b) where
  μ := X.μ
  Tw := X.Tw
  D := (lv (fc X.zs) b).dQ Bs.μ0
  XE := X.XE cr b
  Ep := X.Ep cr b
  ι := X.rowMat cr b
  dW := X.dW b
  XW := X.XW b
  Wp := X.WpK b
  M := X.M b
  θ := X.liftMat cr b
  κ := X.κ
  lam := X.lam
  err0 := X.err0

end Level

end CxData

namespace CxData

variable {Bs : DefBase K} {A : DefAmb Bs} (X : CxData A)

structure CxCol {fc : DefSub A → DefFace Bs} (X : CxData A) where

  B : ∀ u, (Fin ((fc X.zs).Dc.a u) → K) →ₗ[K] Module.Dual K (Fin ((lv (fc X.zs) true).dQ Bs.μ0) → K)

  ζ : (fc X.zs).Dc.Mem → Bs.Tup → K

  sEE : X.EE →ₗ⋆[ℂ] (fc X.zs).Sp.HH

variable {fc : DefSub A → DefFace Bs} (cr : Crd A fc)

def colOf (Y : CxCol (fc := fc) X) : ColData (fc X.zs).Dc (fc X.zs).Sp (X.data cr true) where
  B := Y.B
  ζ := Y.ζ
  sE := Y.sEE.comp (X.iC cr true Bs.μ0)

section Links

variable (b : Bool)

def H0 : Prop := (∀ w, X.μ (Formalism.DivisionValues.conjPl w) = X.μ w) ∧ ∀ w, w ∈ X.Tw ↔ X.μ w ≠ Bs.μ0

def H4pos : Prop := (∀ v, 0 < X.κ v) ∧ (∀ j t p v, 0 < X.lam j t p v) ∧ ∀ b, 0 < X.nP b

def RatZ : Prop :=
  (∀ t, Submodule.span ℂ ((X.jR t) '' (X.Z t : Set (A.FR t))) = LinearMap.range (LinearMap.adjoint (X.Θ t))) ∧
  ∀ j t, Submodule.span ℂ ((X.jL j t) '' (X.Zl j t : Set (A.FL j t))) = LinearMap.range (LinearMap.adjoint (X.θ' j t))

def H2 : Prop :=
  Function.Injective (X.iC cr b Bs.μ0) ∧
    (∀ t, Function.Injective (X.iC cr b t) ∧ LinearMap.range (X.iC cr b t) = LinearMap.range (X.iC cr b Bs.μ0)) ∧
    LinearMap.range (X.iC cr b Bs.μ0) = X.EEl b

def RATmu : Prop := ∀ t, IsRat Bs.v0.embedding (X.rowMatC cr b t)

def H3 : Prop :=
  ∀ p (x : Fin ((lv (fc X.zs) b).dQ Bs.μ0) → K),
    x ∈ (lv (fc X.zs) b).Qp Bs.μ0 p ↔ X.iC cr b Bs.μ0 (cpt Bs.v0.embedding x) ∈ X.EEp p

def H4 : Prop :=
  ∀ t p (x : Fin ((lv (fc X.zs) b).dQ t) → K), X.iC cr b t (cpt Bs.v0.embedding x) ∈ X.EEp p →
    ∀ y : Fin ((lv (fc X.zs) b).dQ t) → K,
      ⟪X.iC cr b t (cpt Bs.v0.embedding x), X.iC cr b t (cpt Bs.v0.embedding y)⟫_ℂ =
        ((X.nP b * (X.κ Bs.v0 * ∏ j, X.lam j t p Bs.v0) : ℝ) : ℂ) *
          Formalism.HermitianLatticesTheory.majAt (Pi.basisFun K _) ((lv (fc X.zs) b).XQ t) Bs.v0 x y

def PartsOrth : Prop :=
  ∀ v, v ≠ Bs.v0 → ∀ p q, p ≠ q → ∀ x ∈ (lv (fc X.zs) b).Qp Bs.μ0 p, ∀ y ∈ (lv (fc X.zs) b).Qp Bs.μ0 q,
    Formalism.HermitianLatticesTheory.majAt (Pi.basisFun K _) ((lv (fc X.zs) b).XQ Bs.μ0) v x y = 0

def KForm : Prop :=
  ∀ j v, LinearIndependent ℂ (X.bW b j v) ∧ Submodule.span ℂ (Set.range (X.bW b j v)) = ⊤

def EWnorm : Prop := ∀ j (x y : X.WC b j Bs.v0), ⟪X.eW b j x, X.eW b j y⟫_ℂ = ((X.nP b : ℝ) : ℂ) * ⟪x, y⟫_ℂ

def MLat : Prop := ∀ j, Submodule.IsLattice K (X.M b j)

def H5 : Prop :=
  ∀ j t, Function.Injective (X.tC cr b j t) ∧ LinearMap.range (X.tC cr b j t) = LinearMap.range (X.w0C b j)

def RATth : Prop := ∀ j t, IsRat Bs.v0.embedding (X.liftMatC cr b j t)

def H3W : Prop :=
  ∀ j p (x : Fin ((lv (fc X.zs) b).dZ j Bs.μ0) → K),
    x ∈ (lv (fc X.zs) b).Zp j Bs.μ0 p ↔ X.tC cr b j Bs.μ0 (cpt Bs.v0.embedding x) ∈ X.Wp j p

def ThmA : Prop :=
  ∀ j t p (x : Fin ((lv (fc X.zs) b).dZ j t) → K), X.tC cr b j t (cpt Bs.v0.embedding x) ∈ X.Wp j p →
    ∀ y : Fin ((lv (fc X.zs) b).dZ j t) → K,
      ⟪X.tC cr b j t (cpt Bs.v0.embedding x), X.tC cr b j t (cpt Bs.v0.embedding y)⟫_ℂ =
        ((X.nP b * X.lam j t p Bs.v0 : ℝ) : ℂ) * Formalism.HermitianLatticesTheory.majAt (Pi.basisFun K _) ((lv (fc X.zs) b).XT j t) Bs.v0 x y

def GalD : Prop :=
  ∀ j v, v ≠ Bs.v0 → ∀ p (x : Fin ((lv (fc X.zs) b).dZ j Bs.μ0) → K),
    X.tC cr b j Bs.μ0 (cpt Bs.v0.embedding x) ∈ X.Wp j p → ∀ y : Fin ((lv (fc X.zs) b).dZ j Bs.μ0) → K,
      ⟪X.wC b j v (cpt v.embedding ((X.liftMat cr b j Bs.μ0).mulVec x)),
          X.wC b j v (cpt v.embedding ((X.liftMat cr b j Bs.μ0).mulVec y))⟫_ℂ =
        ((X.lam j Bs.μ0 p v : ℝ) : ℂ) * Formalism.HermitianLatticesTheory.majAt (Pi.basisFun K _) ((lv (fc X.zs) b).XT j Bs.μ0) v x y

end Links

structure CxLinks (X : CxData A) (Y : CxCol (fc := fc) X) (C CH : ℝ) : Prop where

  stable : X.zs.Stable

  inBlock : X.zs.InBlock

  ratZ : X.RatZ

  pos : ∀ b, (lv (fc X.zs) b).Pos

  proviso : ∀ b, (lv (fc X.zs) b).Proviso

  types : ∀ b, (lv (fc X.zs) b).Types

  partsOrth : ∀ b, X.PartsOrth b (fc := fc)

  h0 : X.H0

  h2 : ∀ b, X.H2 cr b

  ratMu : ∀ b, X.RATmu cr b

  h3 : ∀ b, X.H3 cr b

  h4pos : X.H4pos

  h4 : ∀ b, X.H4 cr b

  kForm : ∀ b, X.KForm b

  mLat : ∀ b, X.MLat b

  ewNorm : ∀ b, X.EWnorm b

  h5 : ∀ b, X.H5 cr b

  ratTh : ∀ b, X.RATth cr b

  h3W : ∀ b, X.H3W cr b

  thmA : ∀ b, X.ThmA cr b

  galD : ∀ b, X.GalD cr b

  l1d : ∀ b, (X.data cr b).DimensionsOfPartsAgree

  l3 : (X.data cr false).L3 ((fc X.zs).Z.num C CH)

  on : (X.data cr false).ON ((fc X.zs).Z.num C CH)

  l6 : (X.data cr true).L6 ((fc X.zs).Z.num C CH)

  l1b : (X.colOf cr Y).PairingFactorsThroughPeriods

  l1e : (X.colOf cr Y).L1e

  untw : (X.data cr false).Untwisted ((fc X.zs).Z.num C CH)

  passage : Passage ((fc X.zs).Z.num C CH) (X.data cr false) (X.data cr true)

  fun0 : (X.data cr false).FUN ((fc X.zs).Z.num C CH)

end CxData

end Formalism.IndefR.Cx
