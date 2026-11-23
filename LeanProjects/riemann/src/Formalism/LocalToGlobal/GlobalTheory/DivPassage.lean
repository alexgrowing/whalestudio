import Mathlib
import Formalism.LocalToGlobal.IndefiniteForms.IndefSide
import Formalism.LocalToGlobal.Divisibility.RowLat
import Formalism.LocalToGlobal.Divisibility.DefGroup
import Formalism.BranchSandwichDivisors.StatementL

open Module NumberField IsDedekindDomain
open scoped Matrix ComplexOrder

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.DivPassage

open Formalism.L2.Indef

structure LevelAmb (K : Type) [Field K] [NumberField K] [StarRing K] (D0 D1 : ℕ) where

  Dg : ℕ

  Xg : InfinitePlace K → Matrix (Fin Dg) (Fin Dg) ℂ

  Rg : Submodule (𝓞 K) (Fin Dg → K)

  ep0 : Matrix (Fin Dg) (Fin Dg) K

  ep1 : Matrix (Fin Dg) (Fin Dg) K

  S : Type

  fS : Fintype S

  es : S → Matrix (Fin Dg) (Fin Dg) K

  nS : S → ℕ

  nbar : ℝ

  G : ℕ

  h0 : ℕ

  h1 : ℕ

  ι0 : Matrix (Fin Dg) (Fin D0) K

  ι1 : Matrix (Fin Dg) (Fin D1) K

attribute [instance] LevelAmb.fS

namespace LevelAmb

variable {K : Type} [Field K] [NumberField K] [StarRing K] {D0 D1 : ℕ} (A : LevelAmb K D0 D1)

def partLat (e : Matrix (Fin A.Dg) (Fin A.Dg) K) : Submodule (𝓞 K) (Fin A.Dg → K) :=
  A.Rg ⊓ (LinearMap.range e.mulVecLin).restrictScalars (𝓞 K)

def latticeAtBaseLevel : Submodule (𝓞 K) (Fin A.Dg → K) := A.partLat A.ep0

def latticeAtSharpLevel : Submodule (𝓞 K) (Fin A.Dg → K) := A.partLat A.ep1

def Rs (s : A.S) : Submodule (𝓞 K) (Fin A.Dg → K) := A.partLat (A.ep0 * A.es s)

def img {D : ℕ} (ι : Matrix (Fin A.Dg) (Fin D) K) (L : Submodule (𝓞 K) (Fin D → K)) : Submodule (𝓞 K) (Fin A.Dg → K) :=
  L.map (ι.mulVecLin.restrictScalars (𝓞 K))

def FramesG : Prop := ∀ v, IsUnit (A.Xg v).det

def LatG : Prop := Submodule.IsLattice K A.Rg

def EmbAt {D : ℕ} (ι : Matrix (Fin A.Dg) (Fin D) K) (ep : Matrix (Fin A.Dg) (Fin A.Dg) K) (h : ℕ)
    (XE : InfinitePlace K → Matrix (Fin D) (Fin D) ℂ) : Prop :=
  Function.Injective ι.mulVec ∧ LinearMap.range ι.mulVecLin = LinearMap.range ep.mulVecLin ∧
    ∀ v (x y : Fin D → K), Formalism.HermitianLatticesTheory.majAt (Pi.basisFun K (Fin D)) XE v x y =
      Formalism.HermitianLatticesTheory.majAt (Pi.basisFun K (Fin A.Dg)) (Formalism.BranchingDeterminantCap.scaleFrame (Real.sqrt h) A.Xg) v (ι *ᵥ x) (ι *ᵥ y)

def SandAt {D : ℕ} (ι : Matrix (Fin A.Dg) (Fin D) K) (ep : Matrix (Fin A.Dg) (Fin A.Dg) K) (h : ℕ)
    (RR : Submodule (𝓞 K) (Fin D → K)) : Prop :=
  A.img ι RR ≤ A.partLat ep ∧ ∀ y ∈ A.partLat ep, (h : 𝓞 K) • y ∈ A.img ι RR

def Sizes (la : ℝ) : Prop :=
  0 < A.h0 ∧ A.h0 ≤ A.G ∧ 0 < A.h1 ∧ A.h1 ≤ A.G ∧ Real.log A.G ≤ la

def Ranks : Prop :=
  Formalism.HN.rkK A.latticeAtBaseLevel = ∑ s, Formalism.HN.rkK (A.Rs s) ∧ Formalism.HN.rkK A.latticeAtSharpLevel = ∑ s, A.nS s * Formalism.HN.rkK (A.Rs s)

def Deg0 : Prop :=
  Formalism.BranchingDeterminantCap.degD (Pi.basisFun K (Fin A.Dg)) A.Xg A.latticeAtBaseLevel ≤
    (∑ s, Formalism.BranchingDeterminantCap.degD (Pi.basisFun K (Fin A.Dg)) A.Xg (A.Rs s)) +
      2 * Real.log A.G * (Formalism.HN.rkK A.latticeAtBaseLevel : ℝ)

def Deg1 : Prop :=
  (∑ s, (A.nS s : ℝ) * Formalism.BranchingDeterminantCap.degD (Pi.basisFun K (Fin A.Dg)) A.Xg (A.Rs s)) -
      17 / 2 * Real.log A.G * (Formalism.HN.rkK A.latticeAtSharpLevel : ℝ) ≤
    Formalism.BranchingDeterminantCap.degD (Pi.basisFun K (Fin A.Dg)) A.Xg A.latticeAtSharpLevel

def MaxT : Prop :=
  Formalism.HN.muMaxDef (Pi.basisFun K (Fin A.Dg)) A.Xg A.latticeAtSharpLevel ≤
    Formalism.HN.muMaxDef (Pi.basisFun K (Fin A.Dg)) A.Xg A.latticeAtBaseLevel + 17 / 2 * Real.log A.G

def Mult (de : ℝ) : Prop :=
  0 < A.nbar ∧ ∀ s, (1 - de) * A.nbar ≤ (A.nS s : ℝ) ∧ (A.nS s : ℝ) ≤ (1 + de) * A.nbar

def RowsG : Prop := A.latticeAtBaseLevel ≠ ⊥ ∧ A.latticeAtSharpLevel ≠ ⊥

end LevelAmb

def PassageFromLevels : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K] (Bs : DefBase K) (Df0 Df1 : DefSide Bs)
    (N : IndefNum Bs) (S0 : IndefData Df0) (S1 : IndefData Df1) (A : LevelAmb K S0.D S1.D),
    A.FramesG → A.LatG → A.EmbAt A.ι0 A.ep0 A.h0 S0.XE → A.EmbAt A.ι1 A.ep1 A.h1 S1.XE →
    A.SandAt A.ι0 A.ep0 A.h0 S0.RR → A.SandAt A.ι1 A.ep1 A.h1 S1.RR → A.Sizes N.la →
    A.Ranks → A.Deg0 → A.Deg1 → A.MaxT → A.Mult N.de → A.RowsG →
      Passage N S0 S1

def PassageAtBaseSharpLevels : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K] (E : Type) [Field E] [NumberField E]
    (Pg : Finset (Formalism.L2.DIV.Pl E)) (r k : ℕ) [Fintype (Formalism.L2.DIV.G0 Pg r)] (Pl0 T J : Type) [Fintype J]
    (F : Formalism.L2.DIV.DefFam K (Formalism.L2.DIV.G0 Pg r) Pl0 T J) (ψ : ∀ PP : Formalism.L2.DIV.Pl E, AddChar (Formalism.L2.DIV.kP PP) K)
    (Zs : DefSub F.amb) (N : IndefNum F.base)
    (S0 : IndefData (F.side (Formalism.L2.DIV.P0 Pg r ψ).H (Formalism.L2.DIV.P0 Pg r ψ).chi Zs))
    (S1 : IndefData (F.side (Formalism.L2.DIV.Psharp Pg r k ψ).H (Formalism.L2.DIV.Psharp Pg r k ψ).chi Zs))
    (A : LevelAmb K S0.D S1.D),
    A.FramesG → A.LatG → A.EmbAt A.ι0 A.ep0 A.h0 S0.XE → A.EmbAt A.ι1 A.ep1 A.h1 S1.XE →
    A.SandAt A.ι0 A.ep0 A.h0 S0.RR → A.SandAt A.ι1 A.ep1 A.h1 S1.RR → A.Sizes N.la →
    A.Ranks → A.Deg0 → A.Deg1 → A.MaxT → A.Mult N.de → A.RowsG →
      Passage N S0 S1

end Formalism.L2.GlobalTheoryTheory.DivPassage
