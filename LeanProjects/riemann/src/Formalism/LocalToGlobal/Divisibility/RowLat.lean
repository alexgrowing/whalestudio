import Mathlib
import Formalism.LocalToGlobal.Divisibility.GoodPartHermitianSpec
import Formalism.LocalToGlobal.Divisibility.Frames
import Formalism.LocalToGlobal.Columns.HeckeSp
import Formalism.LocalToGlobal.Columns.AlgebraMapMemMaximalIdealPowIff
import Formalism.LocalToGlobal.IndefiniteForms.IndefSide

open Module NumberField IsDedekindDomain Polynomial
open scoped Matrix ComplexOrder

noncomputable section

namespace Formalism.L2.DIV

open Formalism.DivisionValues Formalism.L2.Indef

section Perp

variable {K : Type} [Field K] [StarRing K] {n : ℕ}

def perpOf (H : Matrix (Fin n) (Fin n) K) (Z : Submodule K (Fin n → K)) : Submodule K (Fin n → K) where
  carrier := {x | ∀ z ∈ Z, hform H z x = 0}
  add_mem' := by
    intro x y hx hy z hz
    rw [map_add, hx z hz, hy z hz, add_zero]
  zero_mem' := by
    intro z _
    rw [map_zero]
  smul_mem' := by
    intro a x hx z hz
    rw [map_smul, hx z hz, smul_zero]

end Perp

section Exp

variable {K : Type} [Field K] [NumberField K] {d : ℕ}

def expW (w : HeightOneSpectrum (𝓞 K)) (A B : Submodule (𝓞 K) (Fin d → K)) : ℕ :=
  sInf {J : ℕ | ∀ a ∈ w.asIdeal ^ J, ∀ z ∈ A, a • z ∈ Formalism.HermitianLatticesTheory.localization₂ w.asIdeal B}

end Exp

structure Lvl (K G : Type) [Field K] [Group G] where

  X : Finset (G → K)

  P : Subgroup G

  ψ : P →* Kˣ

def Lvl.full {K G : Type} [Field K] [Group G] (X : Finset (G → K)) : Lvl K G := ⟨X, ⊥, 1⟩

def CSD.gaOp {K : Type} [Field K] [NumberField K] [StarRing K] (S : CSD K) {G : Type} [Group G] [Fintype G]
    (r : Representation K G S.Forms) (a : MonoidAlgebra K G) : Module.End K S.Forms := ∑ t : G, a.coeff t • r t

structure BlockDat (K : Type) [Field K] [NumberField K] [StarRing K] (G : Type) [Group G] [Fintype G]
    (Pl0 : Type) where

  S : CSD K

  r : Representation K G S.Forms

  Pl : Type

  pl : Pl → Pl0

  q : Pl → ℕ

  n : ℕ

  t : ℕ

  op : Pl × ℕ → Module.End K S.Forms

  bl : List (Pl → K)

namespace BlockDat

variable {K : Type} [Field K] [NumberField K] [StarRing K] {G : Type} [Group G] [Fintype G] {Pl0 : Type}
  (B : BlockDat K G Pl0) (ℓ : Lvl K G)

def blockProd (P : B.Pl) : K[X] := (B.bl.map fun ν => Col.blockPoly (ν P) (B.q P) B.t).prod

def ZH : Submodule K B.S.Forms := Col.blockSum B.n B.q B.t B.bl B.op

def HasRes (Sg : Pl0 → K[X]) (x : B.Pl × ℕ → K) : Prop :=
  ∀ P, Col.heckePoly B.n B.q x P = Sg (B.pl P) * B.blockProd P

def partF (Sg : Pl0 → K[X]) : Submodule K B.S.Forms := Col.eigSum B.op (B.HasRes Sg)

def goodF (X : Finset (G → K)) : Submodule K B.S.Forms :=
  LinearMap.range (B.S.gaOp B.r (goodAt X (⊥ : Subgroup G) 1))

def ZHg (X : Finset (G → K)) : Submodule K B.S.Forms := B.ZH ⊓ B.goodF X

def coord (W : Submodule K B.S.Forms) : Submodule K (Fin B.S.dim → K) :=
  W.map (B.S.basis.equivFun : B.S.Forms →ₗ[K] (Fin B.S.dim → K))

def opMat (i : B.Pl × ℕ) : Matrix (Fin B.S.dim) (Fin B.S.dim) K :=
  LinearMap.toMatrix B.S.basis B.S.basis (B.op i)

abbrev nV : ℕ := B.S.BaseDimension B.r ℓ.X ℓ.P ℓ.ψ

def vE : Matrix (Fin B.S.dim) (Fin (B.nV ℓ)) K := B.S.V0E B.r ℓ.X ℓ.P ℓ.ψ

def vPr : Matrix (Fin (B.nV ℓ)) (Fin B.S.dim) K := B.S.goodPartProjection B.r ℓ.X ℓ.P ℓ.ψ

def HV : Matrix (Fin (B.nV ℓ)) (Fin (B.nV ℓ)) K := B.S.goodPartHermitianForm B.r ℓ.X ℓ.P ℓ.ψ

def Mt : Submodule (𝓞 K) (Fin (B.nV ℓ) → K) := B.S.Mt B.r ℓ.X ℓ.P ℓ.ψ

def inV0 (W : Submodule K B.S.Forms) : Submodule K (Fin (B.nV ℓ) → K) :=
  (B.coord W).comap (B.vE ℓ).mulVecLin

def invariantGoodPart : Submodule K (Fin (B.nV ℓ) → K) := B.inV0 ℓ B.ZH

def resSet (X : Finset (G → K)) : Set (Pl0 → K[X]) :=
  {Sg | (∀ P0, P0 ∉ Set.range B.pl → Sg P0 = 1) ∧ B.inV0 (Lvl.full X) (B.partF Sg) ≠ ⊥}

open Classical in

def ixFin (X : Finset (G → K)) : Finset (Pl0 → K[X]) :=
  if h : (B.resSet X).Finite then h.toFinset else ∅

section Sub

variable (Z : Submodule K B.S.Forms)

def ZStable : Prop := (∀ i, Z ≤ Z.comap (B.op i)) ∧ ∀ g, Z ≤ Z.comap (B.r g)

def Z0 : Submodule K (Fin (B.nV ℓ) → K) := B.inV0 ℓ Z

def U : Submodule K (Fin (B.nV ℓ) → K) := perpOf (B.HV ℓ) (B.Z0 ℓ Z)

abbrev dZ : ℕ := subDim (B.Z0 ℓ Z)

def zE : Matrix (Fin (B.nV ℓ)) (Fin (B.dZ ℓ Z)) K := subE (B.Z0 ℓ Z)

def Pq : Matrix (Fin (B.dZ ℓ Z)) (Fin (B.nV ℓ)) K := orthPr (B.HV ℓ) (B.zE ℓ Z)

def HZ : Matrix (Fin (B.dZ ℓ Z)) (Fin (B.dZ ℓ Z)) K := (B.zE ℓ Z)ᴴ * B.HV ℓ * B.zE ℓ Z

def XQ : InfinitePlace K → Matrix (Fin (B.dZ ℓ Z)) (Fin (B.dZ ℓ Z)) ℂ := quotFrame (B.Pq ℓ Z) (B.HV ℓ)

def fE : Matrix (Fin B.S.dim) (Fin (B.dZ ℓ Z)) K := B.vE ℓ * B.zE ℓ Z

def lPr : Matrix (Fin (B.dZ ℓ Z)) (Fin (B.S.lvlDim B.r ℓ.P ℓ.ψ)) K :=
  B.Pq ℓ Z * B.vPr ℓ * B.S.lvlE B.r ℓ.P ℓ.ψ

def abelian₂ : Submodule (𝓞 K) (Fin (B.dZ ℓ Z) → K) := matLat (B.Pq ℓ Z) (B.Mt ℓ)

def Tl : Submodule (𝓞 K) (Fin (B.dZ ℓ Z) → K) := matLat (B.lPr ℓ Z) (B.S.lvlNab B.r ℓ.P ℓ.ψ)

def cutZ : Submodule (𝓞 K) (Fin (B.dZ ℓ Z) → K) := cutLat (B.fE ℓ Z) B.S.nabLat

def delZ : Submodule (𝓞 K) (Fin (B.dZ ℓ Z) → K) := cutLat (B.fE ℓ Z) B.S.delLat

def JexpW (w : HeightOneSpectrum (𝓞 K)) : ℕ := expW w (B.cutZ ℓ Z) (B.delZ ℓ Z)

def JexpU (w : HeightOneSpectrum (𝓞 K)) : ℚ := (B.JexpW ℓ Z w : ℚ) / (Col.eW w : ℚ)

def part (Sg : Pl0 → K[X]) : Submodule K (Fin (B.dZ ℓ Z) → K) :=
  (B.inV0 ℓ (B.partF Sg)).comap (B.zE ℓ Z).mulVecLin

def toF : (Fin (B.dZ ℓ Z) → K) →ₗ[K] B.S.Forms :=
  (B.S.basis.equivFun.symm : (Fin B.S.dim → K) →ₗ[K] B.S.Forms) ∘ₗ (B.vE ℓ).mulVecLin ∘ₗ
    (B.zE ℓ Z).mulVecLin

end Sub

def PrIsSpectral (hc : Col.PairComm B.op) (hs : Col.SplitOver B.op) : Prop :=
  ∀ u : Fin (B.nV ℓ) → K, B.toF ℓ B.ZH ((B.Pq ℓ B.ZH).mulVec u) =
    Col.eigProj hc hs (Col.HasBlocks B.n B.q B.t B.bl) (B.S.basis.equivFun.symm ((B.vE ℓ).mulVec u))

structure Ok (s : ℕ) : Prop where

  good : B.S.Good s

  hrat : ∀ i j, B.S.H i j ∈ cmMax K

  hpos : ∀ v : InfinitePlace K, (B.S.H.map v.embedding).PosDef

  act : B.S.ActGood B.r

  actRat : B.S.ActRat B.r

  comm : Col.PairComm B.op

  split : Col.SplitOver B.op

  opG : ∀ i g, Commute (B.op i) (B.r g)

  blocks : Col.BlockOk B.t B.bl

  q_pos : ∀ P, 0 < B.q P

  pl_inj : Function.Injective B.pl

end BlockDat

structure DefFam (K : Type) [Field K] [NumberField K] [StarRing K] (G : Type) [Group G] [Fintype G]
    (Pl0 T J : Type) where

  v0 : InfinitePlace K

  μ0 : T

  X : Finset (G → K)

  R : T → BlockDat K G Pl0

  L : J → T → BlockDat K G Pl0

  tr : J → (Pl0 → K[X]) → Pl0 → K[X]

namespace DefFam

variable {K : Type} [Field K] [NumberField K] [StarRing K] {G : Type} [Group G] [Fintype G]
  {Pl0 T J : Type} [Fintype J] (F : DefFam K G Pl0 T J)

@[reducible] def base : DefBase K where
  K0 := cmMax K
  v0 := F.v0
  Tup := T
  μ0 := F.μ0
  Ix := ↥((F.R F.μ0).ixFin F.X)
  fIx := inferInstance
  J := J
  fJ := inferInstance

@[reducible] def amb : DefAmb F.base where
  FR t := (F.R t).S.Forms
  aR _ := inferInstance
  mR _ := inferInstance
  OpR t := ((F.R t).Pl × ℕ) ⊕ G
  opR t := Sum.elim (F.R t).op fun g => (F.R t).r g
  ZHR t := (F.R t).ZHg F.X
  FL j t := (F.L j t).S.Forms
  aL _ _ := inferInstance
  mL _ _ := inferInstance
  OpL j t := ((F.L j t).Pl × ℕ) ⊕ G
  opL j t := Sum.elim (F.L j t).op fun g => (F.L j t).r g
  ZHL j t := (F.L j t).ZHg F.X

def lvl (P : Subgroup G) (ψ : P →* Kˣ) : Lvl K G := ⟨F.X, P, ψ⟩

def lvlA (P : Subgroup G) (ψ : P →* Kˣ) : Lvl K G := ⟨F.X, P, ψ⁻¹⟩

def side (P : Subgroup G) (ψ : P →* Kˣ) (Zs : DefSub F.amb) : DefSide F.base where
  nV t := (F.R t).nV (F.lvl P ψ)
  HV t := (F.R t).HV (F.lvl P ψ)
  Mt t := (F.R t).Mt (F.lvl P ψ)
  dQ t := (F.R t).dZ (F.lvl P ψ) (Zs.Z t)
  Pq t := (F.R t).Pq (F.lvl P ψ) (Zs.Z t)
  XQ t := (F.R t).XQ (F.lvl P ψ) (Zs.Z t)
  Qp t p := (F.R t).part (F.lvl P ψ) (Zs.Z t) p.1
  dZ j t := (F.L j t).dZ (F.lvlA P ψ) (Zs.Zl j t)
  HT j t := (F.L j t).HZ (F.lvlA P ψ) (Zs.Zl j t)
  XT j t := (F.L j t).XQ (F.lvlA P ψ) (Zs.Zl j t)
  Tl j t := (F.L j t).Tl (F.lvlA P ψ) (Zs.Zl j t)
  Zp j t p := (F.L j t).part (F.lvlA P ψ) (Zs.Zl j t) (F.tr j p.1)

def J0 (P : Subgroup G) (ψ : P →* Kˣ) (Zs : DefSub F.amb) (t : T) (w : HeightOneSpectrum (𝓞 K)) (j : J) : ℝ :=
  (((F.L j t).JexpU (F.lvlA P ψ) (Zs.Zl j t) w : ℚ) : ℝ)

structure Ok (s : ℕ) : Prop where

  conj : IsConjAt F.v0

  tup_fin : Finite T

  irr : ∀ χ ∈ F.X, IsAbsIrrChar χ

  what₂ : ∀ t, (F.R t).Ok s

  lifts : ∀ j t, (F.L j t).Ok s

def RowsExist (P : Subgroup G) (ψ : P →* Kˣ) (Zs : DefSub F.amb) : Prop :=
  0 < (F.R F.μ0).dZ (F.lvl P ψ) (Zs.Z F.μ0)

def IsType (B : BlockDat K G Pl0) (f : (Pl0 → K[X]) → Pl0 → K[X]) (x : B.Pl × ℕ → K) : Prop :=
  ∃ Sg ∈ (F.R F.μ0).ixFin F.X, B.HasRes (f Sg) x

def SameTypes (P : Subgroup G) (ψ : P →* Kˣ) (Zs : DefSub F.amb) : Prop :=
  ∀ j, (F.L j F.μ0).Z0 (F.lvlA P ψ) (Zs.Zl j F.μ0) ≤
    (F.L j F.μ0).inV0 (F.lvlA P ψ) (Col.eigSum (F.L j F.μ0).op (F.IsType (F.L j F.μ0) (F.tr j)))

def TypesSep : Prop :=
  ∀ Sg ∈ (F.R F.μ0).ixFin F.X, ∀ Sg' ∈ (F.R F.μ0).ixFin F.X, Sg ≠ Sg' →
    ∀ j, ∃ P : (F.L j F.μ0).Pl, F.tr j Sg ((F.L j F.μ0).pl P) ≠ F.tr j Sg' ((F.L j F.μ0).pl P)

def LiftRat (P : Subgroup G) (ψ : P →* Kˣ) (Zs : DefSub F.amb) : Prop :=
  ∀ j, SubHasRatBasis ((F.L j F.μ0).Z0 (F.lvlA P ψ) (Zs.Zl j F.μ0))

end DefFam

section Side

variable {K : Type} [Field K] [NumberField K] [StarRing K] {Bs : DefBase K} (Df : DefSide Bs)

open Classical in

def locBasisOf {D : ℕ} (L : Submodule (𝓞 K) (Fin D → K)) (w : HeightOneSpectrum (𝓞 K)) :
    Fin D → Fin D → K :=
  if h : ∃ e, IsLocBasis L w e then h.choose else 0

def ebOf (t : Bs.Tup) (w : HeightOneSpectrum (𝓞 K)) : Fin (Df.dQ t) → Fin (Df.dQ t) → K :=
  locBasisOf (Df.abelian₂ t) w

def GmOf (t : Bs.Tup) (w : HeightOneSpectrum (𝓞 K)) : K := Df.Gm (ebOf Df) t w

open Classical in

def partPr (t : Bs.Tup) (p : Bs.Ix) : Matrix (Fin (Df.dQ t)) (Fin (Df.dQ t)) K :=
  if h : IsCompl (Df.Qp t p) (⨆ (p' : Bs.Ix) (_ : p' ≠ p), Df.Qp t p') then
    LinearMap.toMatrix' ((Df.Qp t p).subtype ∘ₗ Submodule.projectionOnto _ _ h)
  else 0

def rowXE (Y : Matrix (Fin (Df.dQ Bs.μ0)) (Fin (Df.dQ Bs.μ0)) ℂ) (κ : InfinitePlace K → ℝ)
    (lam : Bs.J → Bs.Ix → InfinitePlace K → ℝ) :
    InfinitePlace K → Matrix (Fin (Df.dQ Bs.μ0)) (Fin (Df.dQ Bs.μ0)) ℂ :=
  rowFrame Bs.v0 Y 1 (partPr Df Bs.μ0) (fun p v => κ v * ∏ j, lam j p v) (Df.XQ Bs.μ0)

variable {Df}

def XEDefined (S : IndefData Df) : Prop :=
  ∀ v, v ≠ Bs.v0 → ∀ x y : Fin (Df.dQ Bs.μ0) → K,
    Formalism.HermitianLatticesTheory.majAt (Pi.basisFun K (Fin S.D)) S.XE v ((S.ι Bs.μ0).mulVec x) ((S.ι Bs.μ0).mulVec y) =
      ∑ p, ((S.κ v * ∏ j, S.lam j Bs.μ0 p v : ℝ) : ℂ) *
        Formalism.HermitianLatticesTheory.majAt (Pi.basisFun K (Fin (Df.dQ Bs.μ0))) (Df.XQ Bs.μ0) v
          ((partPr Df Bs.μ0 p).mulVec x) ((partPr Df Bs.μ0 p).mulVec y)

def ccOf (S : IndefData Df) := Formalism.HN.dualLat S.RR

end Side

end Formalism.L2.DIV
