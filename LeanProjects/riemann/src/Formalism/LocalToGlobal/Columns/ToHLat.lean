import Mathlib
import Formalism.LocalToGlobal.Columns.RhoEqOfSmulEq
import Formalism.LocalToGlobal.Columns.GSetLemmas
import Formalism.LocalToGlobal.Columns.ColForms
import Formalism.LocalToGlobal.Columns.ColFormsLemmas
import Formalism.LocalToGlobal.Columns.ScaledRamifiedLattice
import Formalism.LocalToGlobal.Columns.RowForms
import Formalism.LocalToGlobal.Columns.RowFormsLemmas
import Formalism.LocalToGlobal.Divisibility.Frames
import Formalism.LocalToGlobal.Divisibility.GoodPartHermitianSpec
import Formalism.LocalToGlobal.GlobalTheory.HLatOps

open NumberField IsDedekindDomain Module
open scoped Matrix ComplexOrder

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.DivisionValues Formalism.L2.DIV Formalism.L2.GlobalTheoryTheory.HLatOps

namespace GSD

variable {K : Type} [Field K] [NumberField K] [StarRing K] (S : GSD K)

def pairAt (v : InfinitePlace K) (x y : S.V) : ℂ :=
  ∑ i, ∑ j, starRingEnd ℂ (v.embedding (S.bV.repr x i)) * v.embedding (S.gramV i j) * v.embedding (S.bV.repr y j)

def ipAt (h : S.Ok) (v : InfinitePlace K) (φ ψ : S.D → S.V) : ℂ :=
  letI : Fintype S.Cl := h.fintypeCl
  ∑ c : S.Cl, (((S.toCSD h).wt c : ℕ) : ℂ)⁻¹ * S.pairAt v (φ (S.outSec.rep c)) (ψ (S.outSec.rep c))

abbrev hDim (h : S.Ok) : ℕ := (S.toCSD h).dim

def hB (h : S.Ok) : Basis (Fin (S.hDim h)) K S.EqFun := (S.toCSD h).basis.map (S.res h).symm

abbrev hGram (h : S.Ok) : Matrix (Fin (S.hDim h)) (Fin (S.hDim h)) K := (S.toCSD h).H

def PosH (h : S.Ok) : Prop := ∀ v : InfinitePlace K, ((S.hGram h).map v.embedding).PosDef

@[reducible] def toH (h : S.Ok) (L : Submodule (𝓞 K) S.EqFun) : HLat K where
  V := S.EqFun
  ι := Fin (S.hDim h)
  b := S.hB h
  X := stdFrame (S.hGram h)
  L := L

abbrev hCoord (h : S.Ok) : S.EqFun ≃ₗ[K] (Fin (S.hDim h) → K) := S.coordOf h S.outSec

def toHc (h : S.Ok) (L : Submodule (𝓞 K) S.EqFun) : HLat K :=
  toHLat (stdFrame (S.hGram h)) (L.map ((S.hCoord h).toLinearMap.restrictScalars (𝓞 K)))

def delHc (h : S.Ok) : HLat K := toHLat (stdFrame (S.hGram h)) (S.toCSD h).delLat

def nabHc (h : S.Ok) : HLat K := toHLat (stdFrame (S.hGram h)) (S.toCSD h).nabLat

def subZ (h : S.Ok) (U : Submodule K S.EqFun) : Submodule K (Fin (S.hDim h) → K) :=
  U.map (S.hCoord h).toLinearMap

def subEq (h : S.Ok) (U : Submodule K S.EqFun) : U ≃ₗ[K] S.subZ h U := (S.hCoord h).submoduleMap U

abbrev subD (h : S.Ok) (U : Submodule K S.EqFun) : ℕ := subDim (S.subZ h U)

def subB (h : S.Ok) (U : Submodule K S.EqFun) : Basis (Fin (S.subD h U)) K U :=
  (subBasis (S.subZ h U)).map (S.subEq h U).symm

def subMat (h : S.Ok) (U : Submodule K S.EqFun) : Matrix (Fin (S.hDim h)) (Fin (S.subD h U)) K :=
  subE (S.subZ h U)

@[reducible] def subH (h : S.Ok) (U : Submodule K S.EqFun) (L : Submodule (𝓞 K) U) : HLat K where
  V := U
  ι := Fin (S.subD h U)
  b := S.subB h U
  X := restrFrame (S.subMat h U) (S.hGram h)
  L := L

def subIncl (h : S.Ok) (U : Submodule K S.EqFun) (L : Submodule (𝓞 K) U) (L' : Submodule (𝓞 K) S.EqFun) :
    (S.subH h U L).V →ₗ[K] (S.toH h L').V := U.subtype

def isoMat (h : S.Ok) (U : Submodule K S.EqFun) (v : InfinitePlace K) :
    Matrix (Fin (S.hDim h)) (Fin (S.subD h U)) ℂ :=
  (stdFrame (S.hGram h) v)⁻¹ * (S.subMat h U).map v.embedding * restrFrame (S.subMat h U) (S.hGram h) v

end GSD

section Cols

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m) (hX : X.Ok)

@[reducible] def latH (u : Pr.Word) (j : ℕ) : HLat X.K :=
  (colGSD W Ch u j).toH (colOk W Ch hX u j) (ColL W Ch u j)

@[reducible] def latNabH (u : Pr.Word) (j : ℕ) : HLat X.K :=
  (colGSD W Ch u j).toH (colOk W Ch hX u j) (ColLnab W Ch u j)

@[reducible] def Mu0H (u : Pr.Word) : HLat X.K :=
  (colGSD W Ch u 0).toH (colOk W Ch hX u 0) (MfL W Ch u)

@[reducible] def MramH (u : Pr.Word) : HLat X.K :=
  (colGSD W Ch u 0).subH (colOk W Ch hX u 0) (MramV W Ch u) (MramL W Ch u)

def ramInclH (u : Pr.Word) : (MramH W Ch hX u).V →ₗ[X.K] (Mu0H W Ch hX u).V := ramIncl W Ch u

def VrC (u : Pr.Word) (v : InfinitePlace X.K) : Matrix (Mu0H W Ch hX u).ι (MramH W Ch hX u).ι ℂ :=
  (colGSD W Ch u 0).isoMat (colOk W Ch hX u 0) (MramV W Ch u) v

@[reducible] def NlamH (u : Pr.Word) (w : HeightOneSpectrum (𝓞 X.K)) : HLat X.K :=
  withL (MramH W Ch hX u) (NlamG W Ch u w)

end Cols

section Rows

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m) (hX : X.Ok)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (mu : Tup X.F X.E X.K S)

@[reducible] def MtildeH (P : LevFam X.E X.K R.r Pr.vGs) : HLat X.K :=
  (mtildeGSD W Ch sel mu P).toH (mtildeOk W Ch sel mu hX P) (MtildeL W Ch sel mu P)

@[reducible] def MtH (P : LevFam X.E X.K R.r Pr.vGs) (j : ℕ) : HLat X.K :=
  (mtGSD W Ch sel mu P j).toH (mtOk W Ch sel mu hX P j) (MtL W Ch sel mu P j)

end Rows

end Formalism.L2.Col
