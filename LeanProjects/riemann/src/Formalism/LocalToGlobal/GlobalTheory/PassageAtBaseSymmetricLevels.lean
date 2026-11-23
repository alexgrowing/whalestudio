import Mathlib
import Formalism.LocalToGlobal.GlobalTheory.DivPassage

open Module NumberField IsDedekindDomain
open scoped Matrix ComplexOrder

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.DivPassage2

open Formalism.L2.Indef Formalism.L2.GlobalTheoryTheory.DivPassage

section Proj

variable {K : Type} [Field K] {Γ : Type} [Group Γ]

def typeProj [Finite Γ] {n : ℕ} (ρ : Γ →* Matrix (Fin n) (Fin n) K) (H : Subgroup Γ) (χ : H →* Kˣ) :
    Matrix (Fin n) (Fin n) K :=
  haveI : Fintype H := Fintype.ofFinite H
  ((Nat.card H : K)⁻¹) • ∑ h : H, (((χ h)⁻¹ : Kˣ) : K) • ρ (h : Γ)

end Proj

structure RepDat (K : Type) [Field K] [NumberField K] [StarRing K] (Γ : Type) [Group Γ] [Fintype Γ] (D0 D1 : ℕ) where

  Dg : ℕ

  Xg : InfinitePlace K → Matrix (Fin Dg) (Fin Dg) ℂ

  Rg : Submodule (𝓞 K) (Fin Dg → K)

  ρ : Γ →* Matrix (Fin Dg) (Fin Dg) K

  S : Type

  fS : Fintype S

  es : S → Matrix (Fin Dg) (Fin Dg) K

  nS : S → ℕ

  nbar : ℝ

  γ : ∀ s, Fin (nS s) → Γ

  ι0 : Matrix (Fin Dg) (Fin D0) K

  ι1 : Matrix (Fin Dg) (Fin D1) K

attribute [instance] RepDat.fS

namespace RepDat

variable {K : Type} [Field K] [NumberField K] [StarRing K] {Γ : Type} [Group Γ] [Fintype Γ] {D0 D1 : ℕ}
  (B : RepDat K Γ D0 D1)

def amb (H0 : Subgroup Γ) (χ0 : H0 →* Kˣ) (H1 : Subgroup Γ) (χ1 : H1 →* Kˣ) : LevelAmb K D0 D1 where
  Dg := B.Dg
  Xg := B.Xg
  Rg := B.Rg
  ep0 := typeProj B.ρ H0 χ0
  ep1 := typeProj B.ρ H1 χ1
  S := B.S
  fS := B.fS
  es := B.es
  nS := B.nS
  nbar := B.nbar
  G := Fintype.card Γ
  h0 := Nat.card H0
  h1 := Nat.card H1
  ι0 := B.ι0
  ι1 := B.ι1

def maj (v : InfinitePlace K) (x y : Fin B.Dg → K) : ℂ := Formalism.HermitianLatticesTheory.majAt (Pi.basisFun K (Fin B.Dg)) B.Xg v x y

def xMat (ep0 ep1 : Matrix (Fin B.Dg) (Fin B.Dg) K) (s : B.S) (i : Fin (B.nS s)) : Matrix (Fin B.Dg) (Fin B.Dg) K :=
  ep1 * B.es s * B.ρ (B.γ s i) * ep0

def xsMat (ep0 ep1 : Matrix (Fin B.Dg) (Fin B.Dg) K) (s : B.S) (i : Fin (B.nS s)) : Matrix (Fin B.Dg) (Fin B.Dg) K :=
  ep0 * B.ρ (B.γ s i)⁻¹ * B.es s * ep1

def GLat : Prop := ∀ g : Γ, ∀ x ∈ B.Rg, B.ρ g *ᵥ x ∈ B.Rg

def GIso : Prop := ∀ (g : Γ) v (x y : Fin B.Dg → K), B.maj v (B.ρ g *ᵥ x) (B.ρ g *ᵥ y) = B.maj v x y

def EsCentral : Prop := ∀ s (g : Γ), B.es s * B.ρ g = B.ρ g * B.es s

def EsOrth : Prop := (∀ s, B.es s * B.es s = B.es s) ∧ ∀ s t, s ≠ t → B.es s * B.es t = 0

def EsSum : Prop := ∑ s, B.es s = 1

def EsInt : Prop := ∀ s, ∀ x ∈ B.Rg, ((Fintype.card Γ : ℕ) : 𝓞 K) • (B.es s *ᵥ x) ∈ B.Rg

def EsAdj : Prop := ∀ s v (x y : Fin B.Dg → K), B.maj v (B.es s *ᵥ x) y = B.maj v x (B.es s *ᵥ y)

def DimMult (ep0 ep1 : Matrix (Fin B.Dg) (Fin B.Dg) K) : Prop :=
  ∀ s, finrank K (LinearMap.range (ep1 * B.es s).mulVecLin) =
    B.nS s * finrank K (LinearMap.range (ep0 * B.es s).mulVecLin)

def XInj (ep0 ep1 : Matrix (Fin B.Dg) (Fin B.Dg) K) : Prop :=
  ∀ s (a : Fin (B.nS s) → Fin B.Dg → K), (∀ i, a i ∈ LinearMap.range (ep0 * B.es s).mulVecLin) →
    ∑ i, B.xMat ep0 ep1 s i *ᵥ a i = 0 → a = 0

def NsSq : Prop := ∀ s, B.nS s ^ 2 ≤ Fintype.card Γ

end RepDat

def SizesFromRep : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (Γ : Type) [Group Γ] [Fintype Γ] (D0 D1 : ℕ)
    (B : RepDat K Γ D0 D1) (H0 H1 : Subgroup Γ) (χ0 : H0 →* Kˣ) (χ1 : H1 →* Kˣ) (la : ℝ),
    Real.log (Fintype.card Γ : ℕ) ≤ la → (B.amb H0 χ0 H1 χ1).Sizes la

def RowsFromRep : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (Γ : Type) [Group Γ] [Fintype Γ] (D0 D1 : ℕ)
    (B : RepDat K Γ D0 D1) (H0 H1 : Subgroup Γ) (χ0 : H0 →* Kˣ) (χ1 : H1 →* Kˣ)
    (XE0 : InfinitePlace K → Matrix (Fin D0) (Fin D0) ℂ) (XE1 : InfinitePlace K → Matrix (Fin D1) (Fin D1) ℂ),
    (B.amb H0 χ0 H1 χ1).LatG →
    (B.amb H0 χ0 H1 χ1).EmbAt B.ι0 (typeProj B.ρ H0 χ0) (Nat.card H0) XE0 →
    (B.amb H0 χ0 H1 χ1).EmbAt B.ι1 (typeProj B.ρ H1 χ1) (Nat.card H1) XE1 →
    0 < D0 → 0 < D1 → (B.amb H0 χ0 H1 χ1).RowsG

def TransferFromRep : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K] (Γ : Type) [Group Γ] [Fintype Γ]
    (D0 D1 : ℕ) (B : RepDat K Γ D0 D1) (H0 H1 : Subgroup Γ) (χ0 : H0 →* Kˣ) (χ1 : H1 →* Kˣ),
    (B.amb H0 χ0 H1 χ1).FramesG → (B.amb H0 χ0 H1 χ1).LatG → (B.amb H0 χ0 H1 χ1).RowsG →
    B.GLat → B.GIso → B.EsCentral → B.EsOrth → B.EsSum → B.EsInt → B.EsAdj →
    B.DimMult (typeProj B.ρ H0 χ0) (typeProj B.ρ H1 χ1) → B.XInj (typeProj B.ρ H0 χ0) (typeProj B.ρ H1 χ1) →
    B.NsSq →
      (B.amb H0 χ0 H1 χ1).Ranks ∧ (B.amb H0 χ0 H1 χ1).Deg0 ∧ (B.amb H0 χ0 H1 χ1).Deg1 ∧ (B.amb H0 χ0 H1 χ1).MaxT

def PassageFromRep : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K] (Bs : DefBase K) (Df0 Df1 : DefSide Bs)
    (N : IndefNum Bs) (S0 : IndefData Df0) (S1 : IndefData Df1) (Γ : Type) [Group Γ] [Fintype Γ]
    (H0 H1 : Subgroup Γ) (χ0 : H0 →* Kˣ) (χ1 : H1 →* Kˣ) (B : RepDat K Γ S0.D S1.D),
    (B.amb H0 χ0 H1 χ1).FramesG → (B.amb H0 χ0 H1 χ1).LatG →
    (B.amb H0 χ0 H1 χ1).EmbAt B.ι0 (typeProj B.ρ H0 χ0) (Nat.card H0) S0.XE →
    (B.amb H0 χ0 H1 χ1).EmbAt B.ι1 (typeProj B.ρ H1 χ1) (Nat.card H1) S1.XE →
    (B.amb H0 χ0 H1 χ1).SandAt B.ι0 (typeProj B.ρ H0 χ0) (Nat.card H0) S0.RR →
    (B.amb H0 χ0 H1 χ1).SandAt B.ι1 (typeProj B.ρ H1 χ1) (Nat.card H1) S1.RR →
    Real.log (Fintype.card Γ : ℕ) ≤ N.la → (B.amb H0 χ0 H1 χ1).Mult N.de → 0 < S0.D → 0 < S1.D →
    B.GLat → B.GIso → B.EsCentral → B.EsOrth → B.EsSum → B.EsInt → B.EsAdj →
    B.DimMult (typeProj B.ρ H0 χ0) (typeProj B.ρ H1 χ1) → B.XInj (typeProj B.ρ H0 χ0) (typeProj B.ρ H1 χ1) →
    B.NsSq →
      Passage N S0 S1

def PassageAtBaseSymmetricLevels : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K] (E : Type) [Field E] [NumberField E]
    (Pg : Finset (Formalism.L2.DIV.Pl E)) (r ρs k : ℕ) [Fintype (Formalism.L2.DIV.G0 Pg r)] (Pl0 T J : Type) [Fintype J]
    (F : Formalism.L2.DIV.DefFam K (Formalism.L2.DIV.G0 Pg r) Pl0 T J) (ψ : ∀ PP : Formalism.L2.DIV.Pl E, AddChar (Formalism.L2.DIV.kP PP) K)
    (Zs : DefSub F.amb) (N : IndefNum F.base)
    (S0 : IndefData (F.side (Formalism.L2.DIV.P0 Pg r ψ).H (Formalism.L2.DIV.P0 Pg r ψ).chi Zs))
    (S1 : IndefData (F.side (Formalism.L2.DIV.PsharpSym Pg r ρs k ψ).H (Formalism.L2.DIV.PsharpSym Pg r ρs k ψ).chi Zs))
    (A : LevelAmb K S0.D S1.D),
    A.FramesG → A.LatG → A.EmbAt A.ι0 A.ep0 A.h0 S0.XE → A.EmbAt A.ι1 A.ep1 A.h1 S1.XE →
    A.SandAt A.ι0 A.ep0 A.h0 S0.RR → A.SandAt A.ι1 A.ep1 A.h1 S1.RR → A.Sizes N.la →
    A.Ranks → A.Deg0 → A.Deg1 → A.MaxT → A.Mult N.de → A.RowsG →
      Passage N S0 S1

def concAmb {K : Type} [Field K] [NumberField K] [StarRing K] {E : Type} [Field E] [NumberField E]
    (Pg : Finset (Formalism.L2.DIV.Pl E)) (r ρs k : ℕ) [Fintype (Formalism.L2.DIV.G0 Pg r)]
    (ψ : ∀ PP : Formalism.L2.DIV.Pl E, AddChar (Formalism.L2.DIV.kP PP) K) {D0 D1 : ℕ}
    (B : RepDat K (Formalism.L2.DIV.G0 Pg r) D0 D1) : LevelAmb K D0 D1 :=
  B.amb (Formalism.L2.DIV.P0 Pg r ψ).H (Formalism.L2.DIV.P0 Pg r ψ).chi (Formalism.L2.DIV.PsharpSym Pg r ρs k ψ).H
    (Formalism.L2.DIV.PsharpSym Pg r ρs k ψ).chi

def PassageConcrete : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K] (E : Type) [Field E] [NumberField E]
    (Pg : Finset (Formalism.L2.DIV.Pl E)) (r ρs k : ℕ) [Fintype (Formalism.L2.DIV.G0 Pg r)] (Pl0 T J : Type) [Fintype J]
    (F : Formalism.L2.DIV.DefFam K (Formalism.L2.DIV.G0 Pg r) Pl0 T J) (ψ : ∀ PP : Formalism.L2.DIV.Pl E, AddChar (Formalism.L2.DIV.kP PP) K)
    (Zs : DefSub F.amb) (N : IndefNum F.base)
    (S0 : IndefData (F.side (Formalism.L2.DIV.P0 Pg r ψ).H (Formalism.L2.DIV.P0 Pg r ψ).chi Zs))
    (S1 : IndefData (F.side (Formalism.L2.DIV.PsharpSym Pg r ρs k ψ).H (Formalism.L2.DIV.PsharpSym Pg r ρs k ψ).chi Zs))
    (B : RepDat K (Formalism.L2.DIV.G0 Pg r) S0.D S1.D),
    (concAmb Pg r ρs k ψ B).FramesG → (concAmb Pg r ρs k ψ B).LatG →
    (concAmb Pg r ρs k ψ B).EmbAt B.ι0 (concAmb Pg r ρs k ψ B).ep0 (concAmb Pg r ρs k ψ B).h0 S0.XE →
    (concAmb Pg r ρs k ψ B).EmbAt B.ι1 (concAmb Pg r ρs k ψ B).ep1 (concAmb Pg r ρs k ψ B).h1 S1.XE →
    (concAmb Pg r ρs k ψ B).SandAt B.ι0 (concAmb Pg r ρs k ψ B).ep0 (concAmb Pg r ρs k ψ B).h0 S0.RR →
    (concAmb Pg r ρs k ψ B).SandAt B.ι1 (concAmb Pg r ρs k ψ B).ep1 (concAmb Pg r ρs k ψ B).h1 S1.RR →
    Real.log (Fintype.card (Formalism.L2.DIV.G0 Pg r) : ℕ) ≤ N.la → (concAmb Pg r ρs k ψ B).Mult N.de → 0 < S0.D → 0 < S1.D →
    B.GLat → B.GIso → B.EsCentral → B.EsOrth → B.EsSum → B.EsInt → B.EsAdj →
    B.DimMult (concAmb Pg r ρs k ψ B).ep0 (concAmb Pg r ρs k ψ B).ep1 →
    B.XInj (concAmb Pg r ρs k ψ B).ep0 (concAmb Pg r ρs k ψ B).ep1 → B.NsSq →
      Passage N S0 S1

end Formalism.L2.GlobalTheoryTheory.DivPassage2
