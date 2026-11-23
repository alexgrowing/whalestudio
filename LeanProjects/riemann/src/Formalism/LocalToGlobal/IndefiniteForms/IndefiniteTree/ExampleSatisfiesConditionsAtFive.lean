import Mathlib
import Formalism.LocalToGlobal.IndefiniteForms.IndefSide
import Formalism.LocalToGlobal.IndefiniteForms.IndefUse
import Formalism.MirabolicMackeyTheory.MirabolicMackeyProofs.LocalConditionsWeightedConditional
import Formalism.MirabolicMackeyTheory.MirabolicMackeyProofs.RamBasic
import Formalism.MirabolicMackeyTheory.MirabolicMackeyProofs.LocalConditionsGlobalForm
import Formalism.MirabolicMackeyTheory.MirabolicMackeyProofs.AbsorbLocalConditions
import Formalism.MirabolicMackeyTheory.MirabolicMackeyProofs.ErrSum
import Formalism.MirabolicMackeyTheory.MirabolicMackeyProofs.UnipotentNumeric
import Formalism.MirabolicMackeyTheory.MirabolicMackeyProofs.AbsorbLocalConditionsOfExact
import Formalism.QuotientMetricDivisors.HermitianTwistDivisors.SecondComplementParameterBounds

open Module NumberField IsDedekindDomain

noncomputable section

namespace Formalism.L2.Indef.Tree

open Formalism.DivisionValues Formalism.EigenvalueLevelCeiling Formalism.L2.Indef

variable {K : Type} [Field K] [NumberField K] [StarRing K]

structure OnConst where

  C : ℝ

  Cb1 : ℝ

  Cb2 : ℝ

namespace OnConst

def Cb (c : OnConst) : ℝ := c.Cb1 + c.Cb2 + 4

def CE (c : OnConst) : ℝ := 4 * c.C ^ 2 + 25 * c.C + c.Cb + 44

end OnConst

structure OnObj {Bs : DefBase K} {Df : DefSide Bs} (S : IndefData Df) (P : Type) [Group P] [Finite P] (c : OnConst) where

  nZ : Bs.J → ℕ

  ρ : ∀ j, Representation K P (Fin (nZ j) → K)

  U : Subgroup P

  ψ : P → 𝓞 K

  V₀ : ∀ j, Submodule K (Fin (nZ j) → K)

  e : ∀ j, (Fin (nZ j) → K) →ₗ[K] (Fin (nZ j) → K)

  Ms : ∀ j, Submodule (𝓞 K) (Fin (nZ j) → K)

  φ : ∀ j, (Fin (S.dW j) → K) →ₗ[K] (Fin (nZ j) → K)

  Th1 : HeightOneSpectrum (𝓞 K) → ∀ j, Submodule (𝓞 K) (Fin (nZ j) → K)

  Th : HeightOneSpectrum (𝓞 K) → ∀ j, Submodule (𝓞 K) (Fin (nZ j) → K)

  ThK : HeightOneSpectrum (𝓞 K) → ∀ j, Submodule (𝓞 K) (Fin (nZ j) → K)

  Th0 : HeightOneSpectrum (𝓞 K) → ∀ j, Submodule (𝓞 K) (Fin (nZ j) → K)

  ThJ : HeightOneSpectrum (𝓞 K) → ∀ j, Submodule (𝓞 K) (Fin (nZ j) → K)

  X₃ : HeightOneSpectrum (𝓞 K) → ∀ j, Submodule (𝓞 K) (Fin (nZ j) → K)

  σ : HeightOneSpectrum (𝓞 K) → Bs.J → K

  a : HeightOneSpectrum (𝓞 K) → Bs.J → K

  E : HeightOneSpectrum (𝓞 K) → Bs.J → ℕ

  r1 : HeightOneSpectrum (𝓞 K) → Bs.J → ℝ

  r2 : HeightOneSpectrum (𝓞 K) → Bs.J → ℝ

  pde : ℕ

  ε0 : HeightOneSpectrum (𝓞 K) → Bs.J → ℝ

  nX : HeightOneSpectrum (𝓞 K) → Bs.J → ℕ

  θ' : ∀ v j, (Fin (nX v j) → K) →ₗ[K] (Fin (nZ j) → K)

  eX : ∀ v j, (Fin (nX v j) → K) →ₗ[K] (Fin (nX v j) → K)

  pr : ∀ v j, (Fin (nX v j) → K) →ₗ[K] (Fin (nX v j) → K)

  Mt : ∀ v j, Submodule (𝓞 K) (Fin (nX v j) → K)

  nnK : Bs.J → K

  Jp : Bs.J → ℕ → ℝ

  k : ℝ

  m : ℝ

  f : ℝ

  bp : ℝ

  Sc : ℝ

  eta : ℝ

  T : ℝ

  DF : ℝ

  X2 : ℝ

  x : ℝ

  eps : ℝ

  vd : ℝ

  rr : ℝ

  de2 : ℝ

  Nc : ℝ

  wt : Bs.J → ℝ

  th : ℕ → ℝ

  ad : ℕ → ℝ

  T2 : ℕ

  g1 : ℕ

  g2 : ℕ

  q1 : ℕ

  dd : ℕ

  sm : Finset ℕ

def AtPair {Bs : DefBase K} {Df : DefSide Bs} (S : IndefData Df) (Q : HeightOneSpectrum (𝓞 K) → Prop) : Prop :=
  ∀ w ∈ S.Tw, Q w ∧ Q (conjPl w)

namespace OnObj

variable {Bs : DefBase K} {Df : DefSide Bs} {S : IndefData Df} {P : Type} [Group P] [Finite P] {c : OnConst} (O : OnObj S P c)

def C (_O : OnObj S P c) : ℝ := c.C

def Cb1 (_O : OnObj S P c) : ℝ := c.Cb1

def Cb2 (_O : OnObj S P c) : ℝ := c.Cb2

def Zg (j : Bs.J) : Submodule K (Fin (O.nZ j) → K) := eig (O.ρ j) O.U O.ψ ⊓ O.V₀ j

def eJ (v : HeightOneSpectrum (𝓞 K)) (j : Bs.J) : Submodule (𝓞 K) (Fin (O.nZ j) → K) :=
  (O.ThJ v j).map ((O.e j).restrictScalars (𝓞 K))

def Im (v : HeightOneSpectrum (𝓞 K)) (j : Bs.J) : Submodule (𝓞 K) (Fin (O.nZ j) → K) :=
  ((O.Mt v j).map ((O.θ' v j).restrictScalars (𝓞 K))).map ((O.e j).restrictScalars (𝓞 K))

def ImageLattice (v : HeightOneSpectrum (𝓞 K)) (j : Bs.J) : Submodule (𝓞 K) (Fin (O.nZ j) → K) :=
  (((O.Mt v j).map ((O.eX v j).restrictScalars (𝓞 K))).map ((O.pr v j).restrictScalars (𝓞 K))).map
    ((O.θ' v j).restrictScalars (𝓞 K))

def r (v : HeightOneSpectrum (𝓞 K)) (j : Bs.J) : ℝ := if plc v = O.pde then O.r2 v j else O.r1 v j

def e0 (v : HeightOneSpectrum (𝓞 K)) (j : Bs.J) : ℝ := ((O.E v j : ℝ) - (vw v (O.σ v j) : ℝ)) / (ramw v : ℝ)

def vU0 (v : HeightOneSpectrum (𝓞 K)) : ℝ := (vw v ((Nat.card O.U : ℕ) : K) : ℝ) / (ramw v : ℝ)

def xe : ℝ := O.x ^ O.eps

def b : ℝ := Real.exp O.xe

def L : ℝ := Real.log O.b

def B0 : ℝ := O.f * O.m * O.b * O.L

def E1u : ℝ := O.xe * (O.B0 + O.Nc)

def Se : ℝ := O.Sc + O.eta

def Y : ℝ := O.C * O.DF

def A1 (j : Bs.J) : ℝ := O.C * (Real.log O.k * O.m * O.wt j + O.f * O.k * O.Se)

def Akw (j : Bs.J) : ℝ := O.C * O.k * O.wt j

def aE (j : Bs.J) (l : ℕ) : ℝ :=
  O.A1 j / (l : ℝ) + O.Akw j * O.th l + O.T * O.ad l + (if O.X2 < (l : ℝ) then O.Akw j / (l : ℝ) ^ 2 else 0)

def sB (j : Bs.J) : ℝ := O.wt j + O.f * O.Se

def sC (j : Bs.J) : ℝ := O.C * O.m * (2 + O.vd) * (O.wt j + O.f * O.Se)

def β (l : ℕ) : ℝ := if l = O.dd then O.f * O.k * O.bp else 0

def y : ℝ := 1 / (4 * (O.f * O.k) ^ 3)

def d0 (j : Bs.J) : ℝ := (finrank K (eig (O.ρ j) O.U O.ψ) : ℝ)

def Rb (j : Bs.J) : ℝ := 2 * ((O.nZ j : ℝ) * (O.f * O.m * O.b))

def gq (v : HeightOneSpectrum (𝓞 K)) : ℝ := if plc v = O.g1 ∨ plc v = O.g2 then 2 * O.f * O.rr ^ 2 else 0

def nn (v : HeightOneSpectrum (𝓞 K)) (j : Bs.J) : ℝ := (vw v (O.nnK j) : ℝ) / (ramw v : ℝ)

def Bad : Finset ℕ := insert O.g1 (insert O.g2 (insert O.q1 (insert O.dd O.sm)))

def errP (j : Bs.J) (l : ℕ) : ℝ :=
  if l = O.g1 ∨ l = O.g2 then 4 * O.T + 4 * O.f * O.rr ^ 2
  else if l ∈ O.sm then 2 * O.sC j + 2 * O.T + 2
  else if l = O.q1 ∨ l = O.dd then 2 * (O.sB j + O.T + 1) + 4 * O.β l
  else errGood O.Y O.X2 (O.A1 j) (O.Akw j) (O.Akw j) O.T O.th O.ad l

def errl (v : HeightOneSpectrum (𝓞 K)) (j : Bs.J) : ℝ := O.errP j (plc v)

def errOn (w : HeightOneSpectrum (𝓞 K)) (j : Bs.J) : ℝ :=
  O.errl w j + (O.r w j / (ramw w : ℝ) + O.r (conjPl w) j / (ramw (conjPl w) : ℝ)) / ((O.U.index : ℝ) * (S.D : ℝ))

def Cb : ℝ := O.Cb1 + O.Cb2 + 4

def EJ : ℝ := 30 * (O.T2 : ℝ) * O.m * O.b * O.xe ^ 2 + 2 * O.m * O.b

def TjId (j : Bs.J) (v : HeightOneSpectrum (𝓞 K)) (t : Bs.Tup) : Prop :=
  (matLat (S.θ j t) (Df.Tl j t)).map ((O.φ j).restrictScalars (𝓞 K)) = O.ImageLattice v j

end OnObj

section Leaves

variable {Bs : DefBase K} {Df : DefSide Bs} {S : IndefData Df} {P : Type} [Group P] [Finite P] {c : OnConst}

def LeafMackey (O : OnObj S P c) : Prop := IsMackey O.U O.ψ

def LeafSup (O : OnObj S P c) : Prop :=
  ∀ j, IsLatIn ⊤ (O.Ms j) ∧ ∀ g : P, (O.Ms j).map ((O.ρ j g).restrictScalars (𝓞 K)) ≤ O.Ms j

def LeafProj (O : OnObj S P c) : Prop :=
  ∀ j, O.e j ∘ₗ O.e j = O.e j ∧ LinearMap.range (O.e j) = O.V₀ j

def TieCoord (O : OnObj S P c) : Prop :=
  (∀ j, Function.Injective (O.φ j) ∧ LinearMap.range (O.φ j) = O.Zg j ∧
    (S.M j).map ((O.φ j).restrictScalars (𝓞 K)) = cut (O.Zg j) (O.Ms j)) ∧
  ∀ w ∈ S.Tw, ∀ j, O.TjId j w (S.μ w) ∧ O.TjId j (conjPl w) (S.μ w)

def RankRows (S : IndefData Df) : Prop := 0 < S.D ∧ ∀ j, S.dW j = S.D

def LeafSpan (O : OnObj S P c) : Prop :=
  AtPair S fun v => ∀ j, IsLatIn ⊤ (O.Th v j) ∧ IsLatIn ⊤ (O.ThK v j)

def LeafLemmaS (O : OnObj S P c) : Prop :=
  AtPair S fun v => ∀ j, O.Th v j ≤ O.Ms j ∧
    (∀ g : P, (O.Th v j).map ((O.ρ j g).restrictScalars (𝓞 K)) ≤ O.Th v j) ∧
    O.σ v j ≠ 0 ∧ O.Th v j ≤ sc (O.σ v j) (O.ThK v j)

def LatticeIndexBoundAtPairs (O : OnObj S P c) : Prop :=
  (AtPair S fun v => ∀ j, IsLatIn ⊤ (O.Th1 v j) ∧ O.Th1 v j ≤ O.Th v j ∧ O.a v j ≠ 0 ∧
    vw v (O.a v j) = (O.E v j : ℤ) ∧
    ∀ W : Submodule K (Fin (O.nZ j) → K),
      (lix v (cut W (O.Ms j)) (cut W (O.Th1 v j)) : ℝ) ≤ (O.E v j : ℝ) * (finrank K W : ℝ) + O.r v j) ∧
  0 ≤ O.de2 ∧ O.de2 ≤ 1 ∧ (∀ v j, 0 ≤ O.r1 v j ∧ 0 ≤ O.r2 v j) ∧
  ∀ j, ∀ S' : Finset (HeightOneSpectrum (𝓞 K)),
    ∑ v ∈ S', lw v * O.r1 v j ≤ (O.nZ j : ℝ) * (O.f * O.m * O.b * O.de2) ∧
    ∑ v ∈ S', lw v * O.r2 v j ≤ (O.nZ j : ℝ) * (O.f * O.m * O.b * O.de2)

def LeafData (O : OnObj S P c) : Prop :=
  AtPair S fun v => ∀ j, (O.Th0 v j).FG ∧ O.Th0 v j ≤ (eig (O.ρ j) O.U O.ψ).restrictScalars (𝓞 K) ∧
    sc ((Nat.card O.U : ℕ) : K) (cut (eig (O.ρ j) O.U O.ψ) (O.ThK v j)) ≤ O.Th0 v j

def LeafRankJ (O : OnObj S P c) : Prop :=
  AtPair S fun v => ∀ j, IsLatIn (O.Zg j) ((O.Th0 v j).map ((O.e j).restrictScalars (𝓞 K))) ∧
    IsLatIn (O.Zg j) (O.eJ v j) ∧ O.Th0 v j ≤ O.ThJ v j

def LeafIdentity (O : OnObj S P c) : Prop :=
  AtPair S fun v => ∀ j, O.θ' v j ∘ₗ O.eX v j = O.e j ∘ₗ O.θ' v j ∧
    ∀ x ∈ LinearMap.range (O.eX v j), x - O.pr v j x ∈ LinearMap.ker (O.θ' v j)

def LeafTW2 (O : OnObj S P c) : Prop :=
  AtPair S fun v => ∀ j, IsLatIn (O.Zg j) (O.X₃ v j) ∧ IsLatIn (O.Zg j) (O.Im v j) ∧
    Formalism.HermitianLatticesTheory.localization₂ v.asIdeal (O.X₃ v j) ≤ Formalism.HermitianLatticesTheory.localization₂ v.asIdeal (O.Im v j)

def LeafTW1 (O : OnObj S P c) : Prop :=
  (AtPair S fun v => ∀ j, 0 ≤ O.ε0 v j ∧ (lix v (cut (O.Zg j) (O.Ms j)) (O.X₃ v j) : ℝ) ≤
      (lix v (cut (O.Zg j) (O.Ms j)) (O.eJ v j) : ℝ) + (ramw v : ℝ) * O.ε0 v j) ∧
  ∀ w ∈ S.Tw, ∑ j, (O.ε0 w j + O.ε0 (conjPl w) j) ≤ 2 / (plc w : ℝ) ^ 2

def LeafShareI (O : OnObj S P c) : Prop :=
  ∀ j, ∃ ep : ℝ, ep ≤ O.y ∧ (1 - ep) * (O.nZ j : ℝ) ≤ (Nat.card O.U : ℝ) * O.d0 j

def LeafIndexU (O : OnObj S P c) : Prop := (1 - O.y) * (Nat.card O.U : ℝ) ≤ (O.U.index : ℝ)

def LeafBadShare (O : OnObj S P c) : Prop :=
  ∀ j, ∃ del : ℝ, 0 ≤ del ∧ del ≤ 1 / 4 ∧ (1 - del) * O.d0 j ≤ (S.D : ℝ)

def LeafUnip (O : OnObj S P c) : Prop :=
  1 ≤ O.rr ∧ ∀ w ∈ S.Tw, (vw w ((Nat.card O.U : ℕ) : K) : ℝ) =
    (ramw w : ℝ) * (if plc w = O.g1 ∨ plc w = O.g2 then O.f * O.rr * (O.rr - 1) / 2 else 0)

def LeafDepthGood (N : IndefNum Bs) (O : OnObj S P c) : Prop :=
  (∀ l, 0 ≤ O.th l ∧ 0 ≤ O.ad l) ∧
  (∀ Q : Finset ℕ, (∀ p ∈ Q, p.Prime) → ∑ p ∈ Q, O.th p * Real.log (p : ℝ) ≤ O.C / O.k) ∧
  (∀ Q : Finset ℕ, (∀ p ∈ Q, p.Prime) → O.T * ∑ p ∈ Q, O.ad p * Real.log (p : ℝ) ≤ O.C * (O.m * O.b)) ∧
  ∀ w ∈ S.Tw, ¬ (plc w ∈ O.sm ∨ plc w = O.q1 ∨ plc w = O.dd ∨ plc w = O.g1 ∨ plc w = O.g2) → ∀ j,
    ((plc w : ℝ) ≤ O.Y → O.e0 w j ≤ N.F0 w j + O.aE j (plc w) + 1 ∧
      O.e0 (conjPl w) j ≤ N.F0 w j + O.aE j (plc w) + 1) ∧
    (O.Y < (plc w : ℝ) → O.e0 w j = 0 ∧ O.e0 (conjPl w) j = 0 ∧ 0 ≤ N.F0 w j)

def LeafDepthRam (N : IndefNum Bs) (O : OnObj S P c) : Prop :=
  ∀ w ∈ S.Tw, (plc w = O.q1 ∨ plc w = O.dd) → ∀ j,
    O.e0 w j ≤ O.sB j + O.T + 1 ∧ O.e0 (conjPl w) j ≤ O.sB j + O.T + 1 ∧
    (plc w = O.q1 → N.F0 w j = 0) ∧ (plc w = O.dd → -(2 * (O.f * O.k * O.bp)) ≤ N.F0 w j ∧ N.F0 w j ≤ 0)

def LeafDepth2 (N : IndefNum Bs) (O : OnObj S P c) : Prop :=
  ∀ w ∈ S.Tw, plc w ∈ O.sm → ∀ j,
    O.e0 w j ≤ O.sC j + O.T + 1 ∧ O.e0 (conjPl w) j ≤ O.sC j + O.T + 1 ∧ N.F0 w j = 0

def LeafDepthLevel (N : IndefNum Bs) (O : OnObj S P c) : Prop :=
  ∀ w ∈ S.Tw, (plc w = O.g1 ∨ plc w = O.g2) → ∀ j,
    O.e0 w j ≤ 2 * O.T - O.nn w j ∧ O.e0 (conjPl w) j ≤ 2 * O.T - O.nn (conjPl w) j ∧
    O.nn w j + O.nn (conjPl w) j = -(2 * N.F0 w j)

def LeafPage (O : OnObj S P c) : Prop :=
  1 ≤ O.C ∧ 1 ≤ O.k ∧ 1 ≤ O.m ∧ 8 ≤ O.f ∧ 0 ≤ O.T ∧ 0 ≤ O.Sc ∧ 0 ≤ O.eta ∧ 0 ≤ O.bp ∧ 0 ≤ O.vd ∧ 0 ≤ O.Nc ∧
  O.g1.Prime ∧ O.g2.Prime ∧ O.q1.Prime ∧ O.dd.Prime ∧
  O.g1 ≠ O.g2 ∧ O.q1 ≠ O.dd ∧ O.q1 ≠ O.g1 ∧ O.q1 ≠ O.g2 ∧ O.dd ≠ O.g1 ∧ O.dd ≠ O.g2 ∧
  O.g1 ∉ O.sm ∧ O.g2 ∉ O.sm ∧ O.q1 ∉ O.sm ∧ O.dd ∉ O.sm ∧ 1 ≤ O.x

def LeafSizes (O : OnObj S P c) : Prop :=
  (∀ j, 0 ≤ O.wt j ∧ O.wt j ≤ 2 * O.f * O.b) ∧
  1 < O.Y ∧ Real.log O.Y ≤ 2 * O.L ∧ O.Y ≤ O.m * O.b ∧
  O.k * O.Se * O.L ≤ O.m * O.b ∧
  O.k ≤ O.X2 ∧ Real.log O.k ≤ O.L ∧
  1 ≤ O.L

def LeafX (O : OnObj S P c) : Prop := Real.log O.x ≤ O.xe ∧ (O.T2 : ℝ) ≤ O.f

def LeafBad (O : OnObj S P c) : Prop :=
  0 ≤ O.Cb1 ∧ 0 ≤ O.Cb2 ∧ ∀ j,
    (2 * (O.sB j + O.T + 1) + 4 * (O.f * O.k * O.bp)) * Real.log ((O.q1 * O.dd : ℕ) : ℝ) ≤ O.Cb1 * (O.f * O.m * O.b) ∧
    (∑ p ∈ O.sm, Real.log (p : ℝ)) * (2 * O.sC j + 2 * O.T + 2) ≤ O.Cb2 * (O.f * O.m * O.b * O.L) ∧
    (4 * O.T + 4 * O.f * O.rr ^ 2) * Real.log ((O.g1 * O.g2 : ℕ) : ℝ) ≤ 4 * O.b

def LeafJSum (O : OnObj S P c) : Prop :=
  ∀ j, (∀ l, 0 ≤ O.Jp j l) ∧
    ∀ Q : Finset ℕ, (∀ p ∈ Q, p.Prime) → ∑ p ∈ Q, O.Jp j p * Real.log (p : ℝ) ≤ O.EJ

def LeafJExp (N : IndefNum Bs) (O : OnObj S P c) : Prop := ∀ w ∈ S.Tw, ∀ j, N.J0 (S.μ w) w j ≤ O.Jp j (plc w)

def TieErr (O : OnObj S P c) : Prop := ∀ w ∈ S.Tw, ∀ j, S.err0 w j = O.errOn w j

def ErrorConstantMatchesDefinition (N : IndefNum Bs) (O : OnObj S P c) (CE : ℝ) : Prop := ∀ j, N.E1 j = CE * O.E1u

end Leaves

def ONwith {Bs : DefBase K} {Df : DefSide Bs} (S : IndefData Df) (N : IndefNum Bs)
    (err : HeightOneSpectrum (𝓞 K) → Bs.J → ℝ) : Prop :=
  (∀ w ∈ S.Tw, ∑ j, ((S.Iw j (S.μ w) w : ℝ) + (S.Iw j (S.μ w) (conjPl w) : ℝ)) ≤
    (∑ j, (2 * ((ramw w : ℝ) * N.F0 w j) + (ramw w : ℝ) * err w j) +
      (ramw w : ℝ) * (2 / (plc w : ℝ) ^ 2)) * (S.D : ℝ)) ∧
  (∀ w ∈ S.Tw, ∀ j, 0 ≤ err w j) ∧
  ∀ j, ∑ w ∈ S.Tw, lw w * ((ramw w : ℝ) * err w j + (ramw w : ℝ) * N.J0 (S.μ w) w j) ≤ N.E1 j

theorem on_iff_with {Bs : DefBase K} {Df : DefSide Bs} (S : IndefData Df) (N : IndefNum Bs) :
    S.ON N ↔ ONwith S N S.err0 := by
  exact Iff.rfl

theorem rankRows_of {Bs : DefBase K} {Df : DefSide Bs} (R : IndefRows Df) (wf : Df.WF) :
    RankRows R.toIndefData := ⟨R.D_pos, R.dW_eq wf⟩

section Proof

variable {Bs : DefBase K} {Df : DefSide Bs} {S : IndefData Df} {P : Type} [Group P] [Finite P] {c : OnConst}

theorem ramw_pos (v : HeightOneSpectrum (𝓞 K)) : (0 : ℝ) < (ramw v : ℝ) := by
  have h : (1 : ℤ) ≤ ramw v := one_le_ramw v
  have h' : (0 : ℤ) < ramw v := by omega
  exact_mod_cast h'

theorem index_pos (U : Subgroup P) : (0 : ℝ) < (U.index : ℝ) := by
  have hne : U.index ≠ 0 := by
    first
    | exact Subgroup.index_ne_zero_of_finite
    | exact Subgroup.FiniteIndex.index_ne_zero
    | (have h := U.card_mul_index
       have hP : 0 < Nat.card P := Nat.card_pos
       intro h0
       rw [h0, mul_zero] at h
       omega)
  exact_mod_cast Nat.pos_of_ne_zero hne

theorem card_pos (U : Subgroup P) : (0 : ℝ) < (Nat.card U : ℝ) := by
  have h : 0 < Nat.card U := Nat.card_pos
  exact_mod_cast h

theorem matLat_one' {d : ℕ} (L : Submodule (𝓞 K) (Fin d → K)) :
    matLat (1 : Matrix (Fin d) (Fin d) K) L = L := by
  unfold matLat
  rw [Matrix.mulVecLin_one]
  first
  | exact Submodule.map_id L
  | (ext x; simp)

theorem local_bound (O : OnObj S P c) (v : HeightOneSpectrum (𝓞 K)) (j : Bs.J) (t : Bs.Tup)
    (hMk : LeafMackey O) (hSup : LeafSup O) (hProj : LeafProj O)
    (hC : Function.Injective (O.φ j) ∧ LinearMap.range (O.φ j) = O.Zg j ∧
      (S.M j).map ((O.φ j).restrictScalars (𝓞 K)) = cut (O.Zg j) (O.Ms j))
    (hT : O.TjId j v t)
    (hSp : IsLatIn ⊤ (O.Th v j) ∧ IsLatIn ⊤ (O.ThK v j))
    (hS : O.Th v j ≤ O.Ms j ∧ (∀ g : P, (O.Th v j).map ((O.ρ j g).restrictScalars (𝓞 K)) ≤ O.Th v j) ∧
      O.σ v j ≠ 0 ∧ O.Th v j ≤ sc (O.σ v j) (O.ThK v j))
    (h0 : IsLatIn ⊤ (O.Th1 v j) ∧ O.Th1 v j ≤ O.Th v j ∧ O.a v j ≠ 0 ∧ vw v (O.a v j) = (O.E v j : ℤ) ∧
      ∀ W : Submodule K (Fin (O.nZ j) → K),
        (lix v (cut W (O.Ms j)) (cut W (O.Th1 v j)) : ℝ) ≤ (O.E v j : ℝ) * (finrank K W : ℝ) + O.r v j)
    (hD : (O.Th0 v j).FG ∧ O.Th0 v j ≤ (eig (O.ρ j) O.U O.ψ).restrictScalars (𝓞 K) ∧
      sc ((Nat.card O.U : ℕ) : K) (cut (eig (O.ρ j) O.U O.ψ) (O.ThK v j)) ≤ O.Th0 v j)
    (hJ : IsLatIn (O.Zg j) ((O.Th0 v j).map ((O.e j).restrictScalars (𝓞 K))) ∧
      IsLatIn (O.Zg j) (O.eJ v j) ∧ O.Th0 v j ≤ O.ThJ v j)
    (hU : O.θ' v j ∘ₗ O.eX v j = O.e j ∘ₗ O.θ' v j)
    (hK : ∀ x ∈ LinearMap.range (O.eX v j), x - O.pr v j x ∈ LinearMap.ker (O.θ' v j))
    (h2 : IsLatIn (O.Zg j) (O.X₃ v j) ∧ IsLatIn (O.Zg j) (O.Im v j) ∧
      Formalism.HermitianLatticesTheory.localization₂ v.asIdeal (O.X₃ v j) ≤ Formalism.HermitianLatticesTheory.localization₂ v.asIdeal (O.Im v j))
    (h1 : (lix v (cut (O.Zg j) (O.Ms j)) (O.X₃ v j) : ℝ) ≤
      (lix v (cut (O.Zg j) (O.Ms j)) (O.eJ v j) : ℝ) + (ramw v : ℝ) * O.ε0 v j) :
    (idx v (S.M j) (matLat (S.θ j t) (Df.Tl j t)) : ℝ) ≤
      (ramw v : ℝ) * ((O.e0 v j + O.vU0 v) * (S.dW j : ℝ) +
        (O.r v j / (ramw v : ℝ) + (O.nZ j : ℝ) * O.vU0 v) / (O.U.index : ℝ) + O.ε0 v j) := by
  have key := local_conditions_weighted_at_place K (Fin (O.nZ j) → K) v P (O.ρ j) O.U O.ψ hMk (O.V₀ j) (O.e j) (hProj j).1 (hProj j).2
    (O.Ms j) (O.Th1 v j) (O.Th v j) (O.ThK v j) (O.Th0 v j) (O.ThJ v j) (O.X₃ v j)
    (hSup j).1 h0.1 hSp.1 hSp.2 h0.2.1 hS.1 hD.1 hD.2.1 (hSup j).2 hS.2.1 (O.σ v j) hS.2.2.1 hS.2.2.2 hD.2.2
    (O.a v j) (O.E v j) (O.r v j) h0.2.2.1 h0.2.2.2.1 h0.2.2.2.2 hJ.1 hJ.2.1 hJ.2.2 h2.1
    (Fin (O.nX v j) → K) (O.θ' v j) (O.eX v j) (O.pr v j) (O.Mt v j) hU hK h2.2.1 h2.2.2
    ((ramw v : ℝ) * O.ε0 v j) h1 (S.dW j) (O.φ j) hC.1 hC.2.1 (S.M j) (matLat (S.θ j t) (Df.Tl j t)) hC.2.2 hT
  rw [Module.finrank_fin_fun] at key
  have hr : (ramw v : ℝ) ≠ 0 := (ramw_pos v).ne'
  have hi : (O.U.index : ℝ) ≠ 0 := (index_pos O.U).ne'
  have e : (ramw v : ℝ) * ((O.e0 v j + O.vU0 v) * (S.dW j : ℝ) +
        (O.r v j / (ramw v : ℝ) + (O.nZ j : ℝ) * O.vU0 v) / (O.U.index : ℝ) + O.ε0 v j) =
      ((O.E v j : ℝ) - (vw v (O.σ v j) : ℝ) + (vw v ((Nat.card O.U : ℕ) : K) : ℝ)) * (S.dW j : ℝ) +
        (O.r v j + (O.nZ j : ℝ) * (vw v ((Nat.card O.U : ℕ) : K) : ℝ)) / (O.U.index : ℝ) +
          (ramw v : ℝ) * O.ε0 v j := by
    unfold OnObj.e0 OnObj.vU0
    field_simp
    try ring
  first
  | (rw [e]; exact key)
  | linarith [key, e]

theorem L_eq (O : OnObj S P c) : O.L = O.xe := by
  unfold OnObj.L OnObj.b
  exact Real.log_exp _

theorem y_bounds (O : OnObj S P c) (hPg : LeafPage O) : 0 ≤ O.y ∧ O.y ≤ 1 / 8 := by
  obtain ⟨-, hk, -, hf, -⟩ := hPg
  have h1 : 1 ≤ O.f * O.k := by nlinarith
  have h8 : 8 ≤ O.f * O.k := by nlinarith
  have h3 : O.f * O.k ≤ (O.f * O.k) ^ 3 := by
    first
    | exact le_self_pow₀ h1 (by norm_num)
    | exact le_self_pow h1 (by norm_num)
    | nlinarith [mul_le_mul h1 h1 zero_le_one (by linarith)]
  have hpos : 0 < 4 * (O.f * O.k) ^ 3 := by linarith
  unfold OnObj.y
  constructor
  · exact div_nonneg zero_le_one hpos.le
  · rw [div_le_div_iff₀ hpos (by norm_num)]
    linarith

theorem r_nonneg (O : OnObj S P c) (hT0 : LatticeIndexBoundAtPairs O) (v : HeightOneSpectrum (𝓞 K)) (j : Bs.J) : 0 ≤ O.r v j := by
  obtain ⟨-, -, -, hr, -⟩ := hT0
  unfold OnObj.r
  split_ifs
  · exact (hr v j).2
  · exact (hr v j).1

theorem errorTerm_nonneg (O : OnObj S P c) (hPg : LeafPage O) (hSz : LeafSizes O) (hth : ∀ l, 0 ≤ O.th l ∧ 0 ≤ O.ad l)
    (j : Bs.J) (l : ℕ) : 0 ≤ O.errP j l := by
  obtain ⟨hC, hk, hm, hf, hT, hSc, heta, hbp, hvd, -⟩ := hPg
  have hwt : 0 ≤ O.wt j := (hSz.1 j).1
  have hSe : 0 ≤ O.Se := by
    unfold OnObj.Se
    linarith
  have hfSe : 0 ≤ O.f * O.Se := mul_nonneg (by linarith) hSe
  have hsB : 0 ≤ O.sB j := by
    unfold OnObj.sB
    linarith
  have hsC : 0 ≤ O.sC j := by
    unfold OnObj.sC
    exact mul_nonneg (mul_nonneg (mul_nonneg (by linarith) (by linarith)) (by linarith)) (by linarith)
  have hβ : ∀ l, 0 ≤ O.β l := by
    intro l
    unfold OnObj.β
    split_ifs
    · exact mul_nonneg (mul_nonneg (by linarith) (by linarith)) hbp
    · exact le_rfl
  have hA1 : 0 ≤ O.A1 j := by
    unfold OnObj.A1
    exact mul_nonneg (by linarith) (add_nonneg (mul_nonneg (mul_nonneg (Real.log_nonneg hk) (by linarith)) hwt)
      (mul_nonneg (mul_nonneg (by linarith) (by linarith)) hSe))
  have hAkw : 0 ≤ O.Akw j := by
    unfold OnObj.Akw
    exact mul_nonneg (mul_nonneg (by linarith) (by linarith)) hwt
  unfold OnObj.errP
  split_ifs
  · nlinarith [sq_nonneg O.rr]
  · linarith
  · nlinarith [hβ l]
  · unfold errGood
    have hl : (0 : ℝ) ≤ (l : ℝ) := Nat.cast_nonneg l
    by_cases hY : (l : ℝ) ≤ O.Y
    · rw [if_pos hY]
      have e1 : 0 ≤ O.A1 j / (l : ℝ) := div_nonneg hA1 hl
      have e2 : 0 ≤ O.Akw j * O.th l := mul_nonneg hAkw (hth l).1
      have e3 : 0 ≤ O.T * O.ad l := mul_nonneg hT (hth l).2
      have e4 : 0 ≤ (if O.X2 < (l : ℝ) then O.Akw j / (l : ℝ) ^ 2 else 0) := by
        split_ifs
        · exact div_nonneg hAkw (by positivity)
        · exact le_rfl
      linarith
    · rw [if_neg hY]

set_option maxHeartbeats 800000 in

theorem bad_sum (O : OnObj S P c) (hPg : LeafPage O) (hSz : LeafSizes O) (hX : LeafX O) (hBad : LeafBad O) (j : Bs.J) :
    ∑ p ∈ O.Bad, Real.log (p : ℝ) * O.errP j p ≤ O.Cb * (O.f * O.m * O.b * O.L) := by
  obtain ⟨hC, hk, hm, hf, hT, hSc, heta, hbp, hvd, hNc, pg1, pg2, pq1, pdd, h12, hqd, hqg1, hqg2, hdg1, hdg2,
    hg1s, hg2s, hq1s, hdds, hx⟩ := hPg
  obtain ⟨hwt, hY1, hlY, hYmb, hkSe, hkX, hlk, hL1⟩ := hSz
  obtain ⟨hCb1, hCb2, hB⟩ := hBad
  obtain ⟨hBq, hBs, hBg⟩ := hB j
  have hg1 : O.g1 ∉ insert O.g2 (insert O.q1 (insert O.dd O.sm)) := by
    simp only [Finset.mem_insert, not_or]
    exact ⟨h12, Ne.symm hqg1, Ne.symm hdg1, hg1s⟩
  have hg2 : O.g2 ∉ insert O.q1 (insert O.dd O.sm) := by
    simp only [Finset.mem_insert, not_or]
    exact ⟨Ne.symm hqg2, Ne.symm hdg2, hg2s⟩
  have hq : O.q1 ∉ insert O.dd O.sm := by
    simp only [Finset.mem_insert, not_or]
    exact ⟨hqd, hq1s⟩
  have eg1 : O.errP j O.g1 = 4 * O.T + 4 * O.f * O.rr ^ 2 := by
    unfold OnObj.errP
    rw [if_pos (Or.inl rfl : O.g1 = O.g1 ∨ O.g1 = O.g2)]
  have eg2 : O.errP j O.g2 = 4 * O.T + 4 * O.f * O.rr ^ 2 := by
    unfold OnObj.errP
    rw [if_pos (Or.inr rfl : O.g2 = O.g1 ∨ O.g2 = O.g2)]
  have eq1 : O.errP j O.q1 = 2 * (O.sB j + O.T + 1) := by
    unfold OnObj.errP
    rw [if_neg (show ¬(O.q1 = O.g1 ∨ O.q1 = O.g2) from fun h => h.elim hqg1 hqg2), if_neg hq1s,
      if_pos (Or.inl rfl : O.q1 = O.q1 ∨ O.q1 = O.dd)]
    unfold OnObj.β
    rw [if_neg hqd]
    ring
  have edd : O.errP j O.dd = 2 * (O.sB j + O.T + 1) + 4 * (O.f * O.k * O.bp) := by
    unfold OnObj.errP
    rw [if_neg (show ¬(O.dd = O.g1 ∨ O.dd = O.g2) from fun h => h.elim hdg1 hdg2), if_neg hdds,
      if_pos (Or.inr rfl : O.dd = O.q1 ∨ O.dd = O.dd)]
    unfold OnObj.β
    rw [if_pos rfl]
  have es : ∀ p ∈ O.sm, O.errP j p = 2 * O.sC j + 2 * O.T + 2 := by
    intro p hp
    unfold OnObj.errP
    rw [if_neg (show ¬(p = O.g1 ∨ p = O.g2) by rintro (rfl | rfl); exacts [hg1s hp, hg2s hp]), if_pos hp]
  have hsm : ∑ p ∈ O.sm, Real.log (p : ℝ) * O.errP j p =
      (∑ p ∈ O.sm, Real.log (p : ℝ)) * (2 * O.sC j + 2 * O.T + 2) := by
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl (fun p hp => by rw [es p hp])
  unfold OnObj.Bad
  rw [Finset.sum_insert hg1, Finset.sum_insert hg2, Finset.sum_insert hq, Finset.sum_insert hdds, hsm, eg1, eg2, eq1, edd]
  have hg1p : (0 : ℝ) < O.g1 := by exact_mod_cast pg1.pos
  have hg2p : (0 : ℝ) < O.g2 := by exact_mod_cast pg2.pos
  have hq1p : (0 : ℝ) < O.q1 := by exact_mod_cast pq1.pos
  have hddp : (0 : ℝ) < O.dd := by exact_mod_cast pdd.pos
  have lg : Real.log ((O.g1 * O.g2 : ℕ) : ℝ) = Real.log (O.g1 : ℝ) + Real.log (O.g2 : ℝ) := by
    push_cast
    exact Real.log_mul hg1p.ne' hg2p.ne'
  have lq : Real.log ((O.q1 * O.dd : ℕ) : ℝ) = Real.log (O.q1 : ℝ) + Real.log (O.dd : ℝ) := by
    push_cast
    exact Real.log_mul hq1p.ne' hddp.ne'
  rw [lg] at hBg
  rw [lq] at hBq
  have hlq : 0 ≤ Real.log (O.q1 : ℝ) := Real.log_nonneg (by exact_mod_cast pq1.one_lt.le)
  have hb : 0 < O.b := by
    unfold OnObj.b
    exact Real.exp_pos _
  have hfmb : 0 ≤ O.f * O.m * O.b := mul_nonneg (mul_nonneg (by linarith) (by linarith)) hb.le
  have hfm : 1 ≤ O.f * O.m := one_le_mul_of_one_le_of_one_le (by linarith) hm
  have hfmL : 1 ≤ O.f * O.m * O.L := one_le_mul_of_one_le_of_one_le hfm hL1
  have h1 : O.Cb1 * (O.f * O.m * O.b) ≤ O.Cb1 * (O.f * O.m * O.b * O.L) :=
    mul_le_mul_of_nonneg_left (le_mul_of_one_le_right hfmb hL1) hCb1
  have h2 : O.b ≤ O.f * O.m * O.b * O.L := by
    calc O.b = O.b * 1 := (mul_one _).symm
      _ ≤ O.b * (O.f * O.m * O.L) := mul_le_mul_of_nonneg_left hfmL hb.le
      _ = O.f * O.m * O.b * O.L := by ring
  have hBn : 0 ≤ O.f * O.k * O.bp := mul_nonneg (mul_nonneg (by linarith) (by linarith)) hbp
  unfold OnObj.Cb
  linarith [mul_nonneg hBn hlq, hBg, hBq, hBs, h1, h2]

theorem on_core (N : IndefNum Bs) (O : OnObj S P c) (CE : ℝ) (hRk : RankRows S)
    (hMk : LeafMackey O) (hSup : LeafSup O) (hProj : LeafProj O) (hC : TieCoord O)
    (hSp : LeafSpan O) (hS : LeafLemmaS O) (hT0 : LatticeIndexBoundAtPairs O) (hD : LeafData O) (hJ : LeafRankJ O)
    (hI : LeafIdentity O) (h2 : LeafTW2 O) (h1 : LeafTW1 O)
    (hSh : LeafShareI O) (hIU : LeafIndexU O) (hBS : LeafBadShare O) (hUn : LeafUnip O)
    (hG : LeafDepthGood N O) (hR : LeafDepthRam N O) (h2p : LeafDepth2 N O) (hL : LeafDepthLevel N O)
    (hPg : LeafPage O) (hSz : LeafSizes O) (hX : LeafX O) (hBad : LeafBad O)
    (hJS : LeafJSum O) (hJE : LeafJExp N O) (hCE : c.CE ≤ CE) (tE1 : ErrorConstantMatchesDefinition N O CE) : ONwith S N O.errOn := by
  obtain ⟨hDpos, hdW⟩ := hRk
  have hPg' := hPg
  obtain ⟨hC1, hk1, hm1, hf8, hTn, hSc, heta, hbp, hvd, hNc, -⟩ := hPg'
  obtain ⟨hw, hY1, hlY, hYb, hkS, hkX, hlk, hL1⟩ := hSz
  have hSz' : LeafSizes O := ⟨hw, hY1, hlY, hYb, hkS, hkX, hlk, hL1⟩
  obtain ⟨hth, hsth, hsad, hgood⟩ := hG
  have hδ := index_pos O.U
  have hcard := card_pos O.U
  have hDr : (0 : ℝ) < (S.D : ℝ) := by exact_mod_cast hDpos
  have hb0 : 0 < O.b := Real.exp_pos _
  have hLxe : O.L = O.xe := L_eq O
  have hSe : 0 ≤ O.Se := by unfold OnObj.Se; linarith

  have hloc1 : ∀ w ∈ S.Tw, ∀ j, (idx w (S.M j) (matLat (S.θ j (S.μ w)) (Df.Tl j (S.μ w))) : ℝ) ≤
      (ramw w : ℝ) * ((O.e0 w j + O.vU0 w) * (S.dW j : ℝ) +
        (O.r w j / (ramw w : ℝ) + (O.nZ j : ℝ) * O.vU0 w) / (O.U.index : ℝ) + O.ε0 w j) := fun w hw j =>
    local_bound O w j (S.μ w) hMk hSup hProj (hC.1 j) (hC.2 w hw j).1 ((hSp w hw).1 j) ((hS w hw).1 j)
      ((hT0.1 w hw).1 j) ((hD w hw).1 j) ((hJ w hw).1 j) ((hI w hw).1 j).1 ((hI w hw).1 j).2 ((h2 w hw).1 j)
      ((h1.1 w hw).1 j).2
  have hloc2 : ∀ w ∈ S.Tw, ∀ j,
      (idx (conjPl w) (S.M j) (matLat (S.θ j (S.μ w)) (Df.Tl j (S.μ w))) : ℝ) ≤
      (ramw (conjPl w) : ℝ) * ((O.e0 (conjPl w) j + O.vU0 (conjPl w)) * (S.dW j : ℝ) +
        (O.r (conjPl w) j / (ramw (conjPl w) : ℝ) + (O.nZ j : ℝ) * O.vU0 (conjPl w)) / (O.U.index : ℝ) +
          O.ε0 (conjPl w) j) := fun w hw j =>
    local_bound O (conjPl w) j (S.μ w) hMk hSup hProj (hC.1 j) (hC.2 w hw j).2 ((hSp w hw).2 j)
      ((hS w hw).2 j) ((hT0.1 w hw).2 j) ((hD w hw).2 j) ((hJ w hw).2 j) ((hI w hw).2 j).1 ((hI w hw).2 j).2
      ((h2 w hw).2 j) ((h1.1 w hw).2 j).2

  have hy := y_bounds O hPg
  have hsh : ∀ j, (O.nZ j : ℝ) / (O.U.index : ℝ) ≤ 3 * (S.D : ℝ) := by
    intro j
    obtain ⟨ep, hep, hs1⟩ := hSh j
    obtain ⟨del, hdel0, hdel1, hs3⟩ := hBS j
    have hnz : (0 : ℝ) ≤ (O.nZ j : ℝ) := Nat.cast_nonneg _
    have hs1' : (1 - O.y) * (O.nZ j : ℝ) ≤ (Nat.card O.U : ℝ) * O.d0 j :=
      le_trans (mul_le_mul_of_nonneg_right (by linarith) hnz) hs1
    have hd0 : 0 ≤ O.d0 j := by unfold OnObj.d0; exact Nat.cast_nonneg _
    have := share_numeric (O.nZ j : ℝ) (O.d0 j) (S.D : ℝ) (Nat.card O.U : ℝ) (O.U.index : ℝ) O.y O.y del
      hcard hδ hnz hd0 hy.1 le_rfl hy.2 hdel0 hdel1 hs1' hIU hs3
    linarith

  have hv : ∀ w ∈ S.Tw, 0 ≤ O.vU0 w ∧ O.vU0 (conjPl w) = O.vU0 w ∧ 4 * O.vU0 w ≤ O.gq w := by
    intro w hw
    have hρ := ramw_pos w
    refine ⟨?_, ?_, ?_⟩
    · unfold OnObj.vU0
      exact div_nonneg (by exact_mod_cast Formalism.DivisionValues.PlaceSumConjugation.vw_nat_nonneg _ w) hρ.le
    · unfold OnObj.vU0
      rw [Formalism.DivisionValues.PlaceSumConjugation.vw_conj_nat, (ramified_basic_bound K w).2.2.2.1]
    · have h := hUn.2 w hw
      have hv' : O.vU0 w = (if plc w = O.g1 ∨ plc w = O.g2 then O.f * O.rr * (O.rr - 1) / 2 else 0) := by
        unfold OnObj.vU0; rw [h]; field_simp
      rw [hv']
      unfold OnObj.gq
      have hr := hUn.1
      split_ifs
      · nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ O.f) (by linarith : (0 : ℝ) ≤ O.rr)]
      · norm_num

  have hdep : ∀ w ∈ S.Tw, ∀ j, O.e0 w j + O.e0 (conjPl w) j - 2 * N.F0 w j + 2 * O.gq w ≤ O.errl w j := by
    intro w hw j
    have dc := depth_cases (O.e0 w j) (O.e0 (conjPl w) j) (N.F0 w j)
    unfold OnObj.errl OnObj.errP
    by_cases hl : plc w = O.g1 ∨ plc w = O.g2
    · rw [if_pos hl]
      have hg : O.gq w = 2 * O.f * O.rr ^ 2 := if_pos hl
      obtain ⟨a, b, c⟩ := hL w hw hl j
      have := dc.2.2.2.2 O.T (O.nn w j) (O.nn (conjPl w) j) (O.gq w) a b c
      rw [hg] at this ⊢
      linarith
    · rw [if_neg hl]
      have hg : O.gq w = 0 := if_neg hl
      rw [hg]
      by_cases h2' : plc w ∈ O.sm
      · rw [if_pos h2']
        obtain ⟨a, b, c⟩ := h2p w hw h2' j
        have := dc.2.2.2.1 (O.sC j) O.T a b c
        linarith
      · rw [if_neg h2']
        by_cases hr : plc w = O.q1 ∨ plc w = O.dd
        · rw [if_pos hr]
          obtain ⟨a, b, cq, cd⟩ := hR w hw hr j
          have hβ : -(2 * O.β (plc w)) ≤ N.F0 w j ∧ N.F0 w j ≤ 0 := by
            unfold OnObj.β
            split_ifs with hd
            · exact cd hd
            · rw [cq (hr.resolve_right hd)]; norm_num
          have := dc.2.2.1 (O.sB j) O.T (O.β (plc w)) a b hβ.1 hβ.2
          linarith
        · rw [if_neg hr]
          have hng : ¬ (plc w ∈ O.sm ∨ plc w = O.q1 ∨ plc w = O.dd ∨ plc w = O.g1 ∨ plc w = O.g2) := by
            rintro (h | h | h | h | h)
            exacts [h2' h, hr (Or.inl h), hr (Or.inr h), hl (Or.inl h), hl (Or.inr h)]
          have hgg := hgood w hw hng j
          unfold errGood
          by_cases hy' : (plc w : ℝ) ≤ O.Y
          · rw [if_pos hy']
            obtain ⟨a, b⟩ := hgg.1 hy'
            have := dc.1 (O.aE j (plc w)) a b
            show _ ≤ 2 * O.aE j (plc w) + 2
            linarith
          · rw [if_neg hy']
            obtain ⟨a, b, c⟩ := hgg.2 (lt_of_not_ge hy')
            have := dc.2.1 a b c
            linarith

  have hDS : DepthSums O.T (O.C / O.k) (O.C * (O.m * O.b)) O.th O.ad := ⟨hsth, hsad⟩
  let EA : Bs.J → ℝ := fun j =>
    2 * (O.C * (Real.log O.k * O.m * O.wt j + O.f * O.k * O.Se) * Real.log O.Y + O.C * O.k * O.wt j * (O.C / O.k) +
      O.C * (O.m * O.b) + 2.04 * (O.C * O.k * O.wt j) / O.X2 + Real.log 4 * O.Y) +
      ∑ p ∈ O.Bad, Real.log (p : ℝ) * O.errP j p
  have hEA : ∀ j, ∑ w ∈ S.Tw, lw w * ((ramw w : ℝ) * O.errl w j) ≤ EA j := by
    intro j
    have hlk0 : 0 ≤ Real.log O.k := Real.log_nonneg hk1
    have hw0 := (hw j).1
    have hA1 : 0 ≤ O.C * (Real.log O.k * O.m * O.wt j + O.f * O.k * O.Se) := by
      have : 0 ≤ Real.log O.k * O.m * O.wt j := by positivity
      have : 0 ≤ O.f * O.k * O.Se := by positivity
      positivity
    have hA2 : 0 ≤ O.C * O.k * O.wt j := by positivity
    refine local_sum_exact K S.Tw O.Bad (O.errP j)
      (errorTerm_nonneg O hPg hSz' hth j) O.Y O.X2 _ _ _ O.T (O.C / O.k) (O.C * (O.m * O.b)) O.th O.ad hY1
      (by linarith) hA1 hA2 hA2 hTn (fun p => (hth p).1) (fun p => (hth p).2) hDS (fun w => O.errl w j) ?_
    intro w _
    unfold OnObj.errl
    split_ifs with hB
    · exact le_rfl
    · have hB' : ¬ (plc w = O.g1 ∨ plc w = O.g2) ∧ plc w ∉ O.sm ∧ ¬ (plc w = O.q1 ∨ plc w = O.dd) := by
        have e : O.Bad = insert O.g1 (insert O.g2 (insert O.q1 (insert O.dd O.sm))) := rfl
        rw [e] at hB
        simp only [Finset.mem_insert, not_or] at hB
        obtain ⟨a, b, c, d, f⟩ := hB
        exact ⟨by rintro (h | h); exacts [a h, b h], f, by rintro (h | h); exacts [c h, d h]⟩
      unfold OnObj.errP
      rw [if_neg hB'.1, if_neg hB'.2.1, if_neg hB'.2.2]
      exact le_rfl

  have hRb : ∀ j, ∀ S' : Finset (HeightOneSpectrum (𝓞 K)),
      ∑ w ∈ S', lw w * ((ramw w : ℝ) * (O.r w j / (ramw w : ℝ))) ≤ O.Rb j := by
    intro j S'
    obtain ⟨-, hde0, hde1, hr0, hbud⟩ := hT0
    have e : ∑ w ∈ S', lw w * ((ramw w : ℝ) * (O.r w j / (ramw w : ℝ))) = ∑ w ∈ S', lw w * O.r w j :=
      Finset.sum_congr rfl fun w _ => by rw [mul_div_cancel₀ _ (ramw_pos w).ne']
    rw [e]
    have s1 : ∑ w ∈ S', lw w * O.r w j ≤ ∑ w ∈ S', lw w * O.r1 w j + ∑ w ∈ S', lw w * O.r2 w j := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_le_sum fun w _ => ?_
      have hl := lw_nonneg' w
      obtain ⟨a, b⟩ := hr0 w j
      rw [← mul_add]
      refine mul_le_mul_of_nonneg_left ?_ hl
      unfold OnObj.r
      split_ifs <;> linarith
    obtain ⟨b1, b2⟩ := hbud j S'
    have hB : 0 ≤ (O.nZ j : ℝ) * (O.f * O.m * O.b) := by
      have : 0 ≤ O.f * O.m * O.b := by positivity
      positivity
    have hde : (O.nZ j : ℝ) * (O.f * O.m * O.b * O.de2) ≤ (O.nZ j : ℝ) * (O.f * O.m * O.b) := by
      have e2 : (O.nZ j : ℝ) * (O.f * O.m * O.b * O.de2) = ((O.nZ j : ℝ) * (O.f * O.m * O.b)) * O.de2 := by ring
      rw [e2]; exact mul_le_of_le_one_right hB hde1
    unfold OnObj.Rb
    linarith

  have hEJ : ∀ j, ∑ w ∈ S.Tw, lw w * ((ramw w : ℝ) * N.J0 (S.μ w) w j) ≤ O.EJ := by
    intro j
    have e : ∑ w ∈ S.Tw, lw w * ((ramw w : ℝ) * N.J0 (S.μ w) w j) ≤
        ∑ w ∈ S.Tw, lw w * ((ramw w : ℝ) * O.Jp j (plc w)) :=
      Finset.sum_le_sum fun w hw => mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left (hJE w hw j) (ramw_pos w).le) (lw_nonneg' w)
    refine le_trans e (le_trans (place_sum K S.Tw (O.Jp j) (hJS j).1)
      (le_trans (le_of_eq ?_) ((hJS j).2 (S.Tw.image plc) ?_)))
    · exact Finset.sum_congr rfl fun p _ => mul_comm _ _
    · intro p hp
      obtain ⟨w, _, rfl⟩ := Finset.mem_image.mp hp
      exact (ramified_basic_bound K w).1

  have X := local_conditions_global_form K S.D hDpos Bs.Tup S.μ Bs.J S.dW hdW S.M
    (fun j t => matLat (S.θ j t) (Df.Tl j t)) (fun j _ => (1 : Matrix (Fin (S.dW j)) (Fin (S.dW j)) K)) S.Tw
    O.e0 (fun v j => O.r v j / (ramw v : ℝ)) O.ε0 N.F0 O.errl (fun w j => (ramw w : ℝ) * N.J0 (S.μ w) w j)
    O.vU0 O.gq (fun j => (O.nZ j : ℝ)) EA O.Rb (fun _ => O.EJ) (O.U.index : ℝ)
    (∑ w ∈ S.Tw, lw w * ((ramw w : ℝ) * (2 / (plc w : ℝ) ^ 2))) hδ
    (by intro w hw j; simp only [matLat_one']; exact hloc1 w hw j)
    (by intro w hw j; simp only [matLat_one']; exact hloc2 w hw j)
    hsh hv hdep h1.2 hEA hRb hEJ le_rfl
  obtain ⟨c1, c2, -⟩ := X
  refine ⟨?_, ?_, ?_⟩
  · intro w hw
    have h := c1 w hw
    simp only [matLat_one'] at h
    rw [(ramified_basic_bound K w).2.2.2.2] at h
    simp only [IndefData.Iw]
    exact h
  · intro w hw j
    unfold OnObj.errOn
    have := errorTerm_nonneg O hPg hSz' hth j (plc w)
    have h0 := r_nonneg O hT0 w j
    have h0' := r_nonneg O hT0 (conjPl w) j
    have := ramw_pos w
    have := ramw_pos (conjPl w)
    have : 0 ≤ (O.r w j / (ramw w : ℝ) + O.r (conjPl w) j / (ramw (conjPl w) : ℝ)) /
        ((O.U.index : ℝ) * (S.D : ℝ)) := by positivity
    unfold OnObj.errl
    linarith
  · intro j
    have h := c2 j
    simp only [EA] at h
    have hCE : 4 * O.C ^ 2 + 25 * O.C + O.Cb + 44 ≤ CE := hCE
    have hE1 := tE1

    have b1 := budget_numeric (O.nZ j : ℝ) (O.U.index : ℝ) (S.D : ℝ) (O.f * O.m * O.b) hδ hDr
      (mul_nonneg (mul_nonneg (by linarith) (by linarith)) hb0.le) (hsh j)
    have hCb0' : 0 ≤ O.Cb := by unfold OnObj.Cb; linarith [hBad.1, hBad.2.1]

    have hbad := bad_sum O hPg hSz' hX hBad j
    have b2 := absorb_local_conditions_exact O.C O.Cb O.L O.xe O.f O.m O.b O.k (O.wt j) O.Se O.Y O.X2
      (∑ p ∈ O.Bad, Real.log (p : ℝ) * O.errP j p) hC1 hCb0'
      hL1 (le_of_eq hLxe) (by linarith) hm1 hb0 hk1 hlk (hw j).1 (hw j).2 hSe hkS hY1 hlY hYb hkX hbad

    have hxe1 : 1 ≤ O.xe := by rw [← hLxe]; exact hL1
    have hEJb : O.EJ ≤ 32 * O.xe * (O.f * O.m * O.b * O.L) := by
      unfold OnObj.EJ
      rw [hLxe]
      have hmb : 0 ≤ O.m * O.b := mul_nonneg (by linarith) hb0.le
      have hx2 : 1 ≤ O.xe ^ 2 := one_le_pow₀ hxe1
      have hmbx : 0 ≤ O.m * O.b * O.xe ^ 2 := mul_nonneg hmb (sq_nonneg _)
      have t1 : (O.T2 : ℝ) * (O.m * O.b * O.xe ^ 2) ≤ O.f * (O.m * O.b * O.xe ^ 2) :=
        mul_le_mul_of_nonneg_right hX.2 hmbx
      have t2a : O.m * O.b ≤ O.m * O.b * O.xe ^ 2 := le_mul_of_one_le_right hmb hx2
      have t2b : O.m * O.b * O.xe ^ 2 ≤ O.f * (O.m * O.b * O.xe ^ 2) := le_mul_of_one_le_left hmbx (by linarith)
      have e : 32 * O.xe * (O.f * O.m * O.b * O.xe) = 32 * (O.f * (O.m * O.b * O.xe ^ 2)) := by ring
      have e2 : 30 * (O.T2 : ℝ) * O.m * O.b * O.xe ^ 2 = 30 * ((O.T2 : ℝ) * (O.m * O.b * O.xe ^ 2)) := by ring
      have e3 : 2 * O.m * O.b = 2 * (O.m * O.b) := by ring
      rw [e, e2, e3]
      linarith
    have eR : 2 * O.Rb j / ((O.U.index : ℝ) * (S.D : ℝ)) =
        2 * (2 * ((O.nZ j : ℝ) * (O.f * O.m * O.b))) / ((O.U.index : ℝ) * (S.D : ℝ)) := rfl
    have hB0 : 0 ≤ O.f * O.m * O.b * O.L :=
      mul_nonneg (mul_nonneg (mul_nonneg (by linarith) (by linarith)) hb0.le) (by linarith)
    have hxe0 : 0 ≤ O.xe := by linarith
    have hCb0 : 0 ≤ O.Cb := by unfold OnObj.Cb; linarith [hBad.1, hBad.2.1]
    have hfin : (4 * O.C ^ 2 + 25 * O.C + O.Cb + 12) * O.xe * (O.f * O.m * O.b * O.L) +
        32 * O.xe * (O.f * O.m * O.b * O.L) ≤ CE * O.E1u := by
      unfold OnObj.E1u OnObj.B0
      have h1' : 0 ≤ (CE - (4 * O.C ^ 2 + 25 * O.C + O.Cb + 44)) * (O.xe * (O.f * O.m * O.b * O.L)) :=
        mul_nonneg (by linarith) (mul_nonneg hxe0 hB0)
      have hCE0 : 0 ≤ CE := by linarith [sq_nonneg O.C]
      have h2' : 0 ≤ CE * (O.xe * O.Nc) := mul_nonneg hCE0 (mul_nonneg hxe0 hNc)
      have e : CE * (O.xe * (O.f * O.m * O.b * O.L + O.Nc)) -
          ((4 * O.C ^ 2 + 25 * O.C + O.Cb + 12) * O.xe * (O.f * O.m * O.b * O.L) +
            32 * O.xe * (O.f * O.m * O.b * O.L)) =
          (CE - (4 * O.C ^ 2 + 25 * O.C + O.Cb + 44)) * (O.xe * (O.f * O.m * O.b * O.L)) +
            CE * (O.xe * O.Nc) := by ring
      linarith
    rw [hE1 j]
    have e3 : ∑ w ∈ S.Tw, lw w * ((ramw w : ℝ) * O.errOn w j + (ramw w : ℝ) * N.J0 (S.μ w) w j) =
        ∑ w ∈ S.Tw, lw w * ((ramw w : ℝ) * (O.errl w j + (O.r w j / (ramw w : ℝ) +
          O.r (conjPl w) j / (ramw (conjPl w) : ℝ)) / ((O.U.index : ℝ) * (S.D : ℝ))) +
            (ramw w : ℝ) * N.J0 (S.μ w) w j) := rfl
    rw [e3]
    unfold OnObj.Rb at h
    linarith

theorem on_of_leaves (N : IndefNum Bs) (O : OnObj S P c) (CE : ℝ) (hRk : RankRows S)
    (hMk : LeafMackey O) (hSup : LeafSup O) (hProj : LeafProj O) (hC : TieCoord O)
    (hSp : LeafSpan O) (hS : LeafLemmaS O) (hT0 : LatticeIndexBoundAtPairs O) (hD : LeafData O) (hJ : LeafRankJ O)
    (hI : LeafIdentity O) (h2 : LeafTW2 O) (h1 : LeafTW1 O)
    (hSh : LeafShareI O) (hIU : LeafIndexU O) (hBS : LeafBadShare O) (hUn : LeafUnip O)
    (hG : LeafDepthGood N O) (hR : LeafDepthRam N O) (h2p : LeafDepth2 N O) (hL : LeafDepthLevel N O)
    (hPg : LeafPage O) (hSz : LeafSizes O) (hX : LeafX O) (hBad : LeafBad O)
    (hJS : LeafJSum O) (hJE : LeafJExp N O) (hCE : c.CE ≤ CE) (tE1 : ErrorConstantMatchesDefinition N O CE) (tErr : TieErr O) : S.ON N := by
  obtain ⟨c1, c2, c3⟩ := on_core N O CE hRk hMk hSup hProj hC hSp hS hT0 hD hJ hI h2 h1 hSh hIU hBS hUn hG hR h2p hL
    hPg hSz hX hBad hJS hJE hCE tE1
  rw [on_iff_with]
  refine ⟨fun w hw => ?_, fun w hw j => ?_, fun j => ?_⟩
  · simp only [tErr w hw]
    exact c1 w hw
  · rw [tErr w hw j]
    exact c2 w hw j
  · calc ∑ w ∈ S.Tw, lw w * ((ramw w : ℝ) * S.err0 w j + (ramw w : ℝ) * N.J0 (S.μ w) w j)
          = ∑ w ∈ S.Tw, lw w * ((ramw w : ℝ) * O.errOn w j + (ramw w : ℝ) * N.J0 (S.μ w) w j) :=
            Finset.sum_congr rfl (fun w hw => by rw [tErr w hw j])
        _ ≤ N.E1 j := c3 j

theorem on_built (N : IndefNum Bs) (O : OnObj S P c) (CE : ℝ) (hRk : RankRows S)
    (hMk : LeafMackey O) (hSup : LeafSup O) (hProj : LeafProj O) (hC : TieCoord O)
    (hSp : LeafSpan O) (hS : LeafLemmaS O) (hT0 : LatticeIndexBoundAtPairs O) (hD : LeafData O) (hJ : LeafRankJ O)
    (hI : LeafIdentity O) (h2 : LeafTW2 O) (h1 : LeafTW1 O)
    (hSh : LeafShareI O) (hIU : LeafIndexU O) (hBS : LeafBadShare O) (hUn : LeafUnip O)
    (hG : LeafDepthGood N O) (hR : LeafDepthRam N O) (h2p : LeafDepth2 N O) (hL : LeafDepthLevel N O)
    (hPg : LeafPage O) (hSz : LeafSizes O) (hX : LeafX O) (hBad : LeafBad O)
    (hJS : LeafJSum O) (hJE : LeafJExp N O) (hCE : c.CE ≤ CE) (tE1 : ErrorConstantMatchesDefinition N O CE) :
    ({ S with err0 := O.errOn } : IndefData Df).ON N := by
  exact on_core N O CE hRk hMk hSup hProj hC hSp hS hT0 hD hJ hI h2 h1 hSh hIU hBS hUn hG hR h2p hL
    hPg hSz hX hBad hJS hJE hCE tE1

theorem on_of_rows (N : IndefNum Bs) (R : IndefRows Df) (wf : Df.WF) (O : OnObj R.toIndefData P c) (CE : ℝ)
    (hMk : LeafMackey O) (hSup : LeafSup O) (hProj : LeafProj O) (hC : TieCoord O)
    (hSp : LeafSpan O) (hS : LeafLemmaS O) (hT0 : LatticeIndexBoundAtPairs O) (hD : LeafData O) (hJ : LeafRankJ O)
    (hI : LeafIdentity O) (h2 : LeafTW2 O) (h1 : LeafTW1 O)
    (hSh : LeafShareI O) (hIU : LeafIndexU O) (hBS : LeafBadShare O) (hUn : LeafUnip O)
    (hG : LeafDepthGood N O) (hR : LeafDepthRam N O) (h2p : LeafDepth2 N O) (hL : LeafDepthLevel N O)
    (hPg : LeafPage O) (hSz : LeafSizes O) (hX : LeafX O) (hBad : LeafBad O)
    (hJS : LeafJSum O) (hJE : LeafJExp N O) (hCE : c.CE ≤ CE) (tE1 : ErrorConstantMatchesDefinition N O CE) (tErr : TieErr O) : R.toIndefData.ON N := by
  exact on_of_leaves N O CE (rankRows_of R wf) hMk hSup hProj hC hSp hS hT0 hD hJ hI h2 h1 hSh hIU hBS hUn
    hG hR h2p hL hPg hSz hX hBad hJS hJE hCE tE1 tErr

theorem on_of_scale (Z : IndefScale Bs) (Cp CH : ℝ) (R : IndefRows Df) (wf : Df.WF) (O : OnObj R.toIndefData P c)
    (hMk : LeafMackey O) (hSup : LeafSup O) (hProj : LeafProj O) (hC : TieCoord O)
    (hSp : LeafSpan O) (hS : LeafLemmaS O) (hT0 : LatticeIndexBoundAtPairs O) (hD : LeafData O) (hJ : LeafRankJ O)
    (hI : LeafIdentity O) (h2 : LeafTW2 O) (h1 : LeafTW1 O)
    (hSh : LeafShareI O) (hIU : LeafIndexU O) (hBS : LeafBadShare O) (hUn : LeafUnip O)
    (hG : LeafDepthGood (Z.num Cp CH) O) (hR : LeafDepthRam (Z.num Cp CH) O) (h2p : LeafDepth2 (Z.num Cp CH) O)
    (hL : LeafDepthLevel (Z.num Cp CH) O)
    (hPg : LeafPage O) (hSz : LeafSizes O) (hX : LeafX O) (hBad : LeafBad O)
    (hJS : LeafJSum O) (hJE : LeafJExp (Z.num Cp CH) O) (hCE : c.CE ≤ Cp) (hE : Z.E1u = O.E1u) (tErr : TieErr O) :
    R.toIndefData.ON (Z.num Cp CH) := by
  have tE1 : ErrorConstantMatchesDefinition (Z.num Cp CH) O Cp := by
    intro j
    show Cp * Z.E1u = Cp * O.E1u
    rw [hE]
  exact on_of_rows (Z.num Cp CH) R wf O Cp hMk hSup hProj hC hSp hS hT0 hD hJ hI h2 h1 hSh hIU hBS hUn
    hG hR h2p hL hPg hSz hX hBad hJS hJE hCE tE1 tErr

def side_of_leaves (Z : IndefScale Bs) (Cp CH : ℝ) (R : IndefRows Df) (wf : Df.WF) (h3 : R.toIndefData.L3 (Z.num Cp CH))
    (O : OnObj R.toIndefData P c)
    (hMk : LeafMackey O) (hSup : LeafSup O) (hProj : LeafProj O) (hC : TieCoord O)
    (hSp : LeafSpan O) (hS : LeafLemmaS O) (hT0 : LatticeIndexBoundAtPairs O) (hD : LeafData O) (hJ : LeafRankJ O)
    (hI : LeafIdentity O) (h2 : LeafTW2 O) (h1 : LeafTW1 O)
    (hSh : LeafShareI O) (hIU : LeafIndexU O) (hBS : LeafBadShare O) (hUn : LeafUnip O)
    (hG : LeafDepthGood (Z.num Cp CH) O) (hR : LeafDepthRam (Z.num Cp CH) O) (h2p : LeafDepth2 (Z.num Cp CH) O)
    (hL : LeafDepthLevel (Z.num Cp CH) O)
    (hPg : LeafPage O) (hSz : LeafSizes O) (hX : LeafX O) (hBad : LeafBad O)
    (hJS : LeafJSum O) (hJE : LeafJExp (Z.num Cp CH) O) (hCE : c.CE ≤ Cp) (hE : Z.E1u = O.E1u) (tErr : TieErr O) :
    IndefSide Df (Z.num Cp CH) :=
  { R with
    l3 := h3
    on := on_of_scale Z Cp CH R wf O hMk hSup hProj hC hSp hS hT0 hD hJ hI h2 h1 hSh hIU hBS hUn hG hR h2p hL
      hPg hSz hX hBad hJS hJE hCE hE tErr }

end Proof

theorem on_family (c : OnConst) : ∃ CE : ℝ, CE = c.CE ∧
    ∀ (K₁ : Type) [Field K₁] [NumberField K₁] [StarRing K₁] (Bs : DefBase K₁) (Df : DefSide Bs) (R : IndefRows Df),
      Df.WF → ∀ (N : IndefNum Bs) (P : Type) [Group P] [Finite P] (O : OnObj R.toIndefData P c),
      LeafMackey O → LeafSup O → LeafProj O → TieCoord O → LeafSpan O → LeafLemmaS O → LatticeIndexBoundAtPairs O → LeafData O →
      LeafRankJ O → LeafIdentity O → LeafTW2 O → LeafTW1 O → LeafShareI O → LeafIndexU O → LeafBadShare O →
      LeafUnip O → LeafDepthGood N O → LeafDepthRam N O → LeafDepth2 N O → LeafDepthLevel N O → LeafPage O →
      LeafSizes O → LeafX O → LeafBad O → LeafJSum O → LeafJExp N O → ErrorConstantMatchesDefinition N O CE → TieErr O →
      R.toIndefData.ON N := by
  refine ⟨c.CE, rfl, ?_⟩
  intro K₁ _ _ _ Bs Df R wf N P _ _ O hMk hSup hProj hC hSp hS hT0 hD hJ hI h2 h1 hSh hIU hBS hUn hG hR h2p hL
    hPg hSz hX hBad hJS hJE tE1 tErr
  exact on_of_rows N R wf O c.CE hMk hSup hProj hC hSp hS hT0 hD hJ hI h2 h1 hSh hIU hBS hUn hG hR h2p hL
    hPg hSz hX hBad hJS hJE le_rfl tE1 tErr

section Examples₂

variable (K)

def stdLat (n : ℕ) : Submodule (𝓞 K) (Fin n → K) :=
  Submodule.span (𝓞 K) (Set.range (Pi.basisFun K (Fin n)))

theorem stdLat_isLatIn (n : ℕ) : IsLatIn ⊤ (stdLat K n) := by
  refine ⟨Submodule.fg_span (Set.finite_range _), ?_⟩
  unfold stdLat
  rw [Submodule.span_span_of_tower]
  exact (Pi.basisFun K (Fin n)).span_eq

theorem eig_triv (n : ℕ) : eig (1 : Representation K Unit (Fin n → K)) ⊤ (fun _ => (1 : 𝓞 K)) = ⊤ := by
  unfold eig
  refine eq_top_iff.mpr (fun x _ => ?_)
  rw [Submodule.mem_iInf]
  intro u
  rw [LinearMap.mem_ker]
  simp

theorem map_id' {n : ℕ} (A : Submodule (𝓞 K) (Fin n → K)) :
    A.map ((LinearMap.id : (Fin n → K) →ₗ[K] (Fin n → K)).restrictScalars (𝓞 K)) = A := by
  first
  | exact Submodule.map_id A
  | (ext x; simp)

theorem cut_top' {n : ℕ} (A : Submodule (𝓞 K) (Fin n → K)) : cut (⊤ : Submodule K (Fin n → K)) A = A := by
  unfold cut
  simp

theorem sc_one' {n : ℕ} (A : Submodule (𝓞 K) (Fin n → K)) : sc (1 : K) A = A := by
  unfold sc
  rw [one_smul]
  exact map_id' K A

private theorem exists_place_lemma (p : ℕ) (hp : p.Prime) : ∃ w : HeightOneSpectrum (𝓞 K), plc w = p := by
  have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  haveI hmax : (Ideal.span {(p : ℤ)}).IsMaximal :=
    PrincipalIdealRing.isMaximal_of_irreducible hpZ.irreducible
  have hker : RingHom.ker (algebraMap ℤ (𝓞 K)) ≤ Ideal.span {(p : ℤ)} := by
    intro x hx
    rw [RingHom.mem_ker] at hx
    have hx0 : x = 0 := (algebraMap ℤ (𝓞 K)).injective_int (by rw [hx, map_zero])
    rw [hx0]
    exact Ideal.zero_mem _
  obtain ⟨Q, hQmax, hQ⟩ := Ideal.exists_ideal_over_maximal_of_isIntegral (Ideal.span {(p : ℤ)}) hker
  have hpQ : ((p : ℕ) : 𝓞 K) ∈ Q := by
    have h1 : (p : ℤ) ∈ Q.comap (algebraMap ℤ (𝓞 K)) := by
      rw [hQ]
      exact Ideal.mem_span_singleton_self _
    rw [Ideal.mem_comap] at h1
    simpa using h1
  have hQne : Q ≠ ⊥ := by
    intro h0
    rw [h0, Ideal.mem_bot] at hpQ
    exact hp.ne_zero (by exact_mod_cast hpQ)
  refine ⟨⟨Q, hQmax.isPrime, hQne⟩, ?_⟩
  haveI : Nontrivial (𝓞 K ⧸ Q) := by
    first
    | exact Ideal.Quotient.nontrivial_iff.mpr hQmax.ne_top
    | exact Ideal.Quotient.nontrivial hQmax.ne_top
    | exact (Ideal.Quotient.field Q).toNontrivial
  haveI : CharP (𝓞 K ⧸ Q) p := by
    rw [CharP.charP_iff_prime_eq_zero hp]
    have h2 := (Ideal.Quotient.eq_zero_iff_mem).mpr hpQ
    simpa using h2
  exact ringChar.eq (𝓞 K ⧸ Q) p

theorem exists_place3 : ∃ w : HeightOneSpectrum (𝓞 K), plc w = 3 := by
  exact exists_place_lemma K 3 Nat.prime_three

abbrev exampleBs (v0 : InfinitePlace K) : DefBase K where
  K0 := ⊥
  v0 := v0
  Tup := Bool
  μ0 := false
  Ix := Unit
  fIx := inferInstance
  J := Unit
  fJ := inferInstance

abbrev exampleDf (v0 : InfinitePlace K) : DefSide (exampleBs K v0) where
  nV := fun _ => 1
  HV := fun _ => 1
  Mt := fun _ => stdLat K 1
  dQ := fun _ => 1
  Pq := fun _ => 1
  XQ := fun _ _ => 1
  Qp := fun _ _ => ⊤
  dZ := fun _ _ => 1
  HT := fun _ _ => 1
  XT := fun _ _ _ => 1
  Tl := fun _ _ => stdLat K 1
  Zp := fun _ _ _ => ⊤

open Classical in

abbrev exampleIndefiniteData (v0 : InfinitePlace K) (Tw0 : Finset (HeightOneSpectrum (𝓞 K))) (er : ℝ) : IndefData (exampleDf K v0) where
  μ := fun w => decide (w ∈ Tw0)
  Tw := Tw0
  D := 1
  XE := fun _ => 1
  Ep := fun _ => ⊤
  ι := fun _ => 1
  dW := fun _ => 1
  XW := fun _ _ => 1
  Wp := fun _ _ => ⊤
  M := fun _ => stdLat K 1
  θ := fun _ _ => 1
  κ := fun _ => 1
  lam := fun _ _ _ _ => 1
  err0 := fun _ _ => er

abbrev exampleConstants (v0 : InfinitePlace K) (F E : ℝ) : IndefNum (exampleBs K v0) where
  F0 := fun w _ => if plc w = 3 then F else 0
  J0 := fun _ _ _ => 0
  E1 := fun _ => E
  l3 := fun _ => 0
  l6 := fun _ => 0
  hh := 0
  la := 0
  de := 0

abbrev exampleC : OnConst := ⟨1, 2 * Real.log 143, 1⟩

abbrev exampleObject (v0 : InfinitePlace K) (Tw0 : Finset (HeightOneSpectrum (𝓞 K))) : OnObj (exampleIndefiniteData K v0 Tw0 0) Unit exampleC where
  nZ := fun _ => 1
  ρ := fun _ => 1
  U := ⊤
  ψ := fun _ => 1
  V₀ := fun _ => ⊤
  e := fun _ => LinearMap.id
  Ms := fun _ => stdLat K 1
  φ := fun _ => LinearMap.id
  Th1 := fun _ _ => stdLat K 1
  Th := fun _ _ => stdLat K 1
  ThK := fun _ _ => stdLat K 1
  Th0 := fun _ _ => stdLat K 1
  ThJ := fun _ _ => stdLat K 1
  X₃ := fun _ _ => stdLat K 1
  σ := fun _ _ => 1
  a := fun _ _ => 1
  E := fun _ _ => 0
  r1 := fun _ _ => 0
  r2 := fun _ _ => 0
  pde := 0
  ε0 := fun _ _ => 0
  nX := fun _ _ => 1
  θ' := fun _ _ => LinearMap.id
  eX := fun _ _ => LinearMap.id
  pr := fun _ _ => LinearMap.id
  Mt := fun _ _ => stdLat K 1
  nnK := fun _ => 1
  Jp := fun _ _ => 0
  k := 1
  m := 1
  f := 8
  bp := 0
  Sc := 0
  eta := 0
  T := 0
  DF := 3
  X2 := 1
  x := 300
  eps := 1
  vd := 0
  rr := 1
  de2 := 1
  Nc := 0
  wt := fun _ => 0
  th := fun _ => 0
  ad := fun _ => 0
  T2 := 0
  g1 := 5
  g2 := 7
  q1 := 11
  dd := 13
  sm := {2}

variable {K} (v0 : InfinitePlace K) (Tw0 : Finset (HeightOneSpectrum (𝓞 K)))

theorem toy_vw_one (v : HeightOneSpectrum (𝓞 K)) : vw v (1 : K) = 0 := by
  unfold vw
  simp only [FractionalIdeal.spanSingleton_one]
  exact FractionalIdeal.count_one K v

theorem toy_card : Nat.card (⊤ : Subgroup Unit) = 1 := by
  simp

theorem example_eigenspace_eq_top (j : Unit) :
    eig ((exampleObject K v0 Tw0).ρ j) (exampleObject K v0 Tw0).U (exampleObject K v0 Tw0).ψ = ⊤ := by
  exact eig_triv K 1

theorem example_Zg_eq_top (j : Unit) : (exampleObject K v0 Tw0).Zg j = ⊤ := by
  unfold OnObj.Zg
  rw [example_eigenspace_eq_top]
  exact top_inf_eq _

theorem example_xe_eq : (exampleObject K v0 Tw0).xe = 300 := by
  show (300 : ℝ) ^ (1 : ℝ) = 300
  exact Real.rpow_one 300

theorem example_b_eq_exp : (exampleObject K v0 Tw0).b = Real.exp 300 := by
  unfold OnObj.b
  rw [example_xe_eq]

theorem example_L_eq : (exampleObject K v0 Tw0).L = 300 := by
  rw [L_eq, example_xe_eq]

theorem example_b_ge : (301 : ℝ) ≤ (exampleObject K v0 Tw0).b := by
  rw [example_b_eq_exp]
  have := Real.add_one_le_exp (300 : ℝ)
  linarith

theorem example_r_eq_zero (v : HeightOneSpectrum (𝓞 K)) (j : Unit) : (exampleObject K v0 Tw0).r v j = 0 := by
  unfold OnObj.r
  split_ifs <;> rfl

theorem example_ramification_zero (v : HeightOneSpectrum (𝓞 K)) (j : Unit) : (exampleObject K v0 Tw0).e0 v j = 0 := by
  show (((0 : ℕ) : ℝ) - (vw v (1 : K) : ℝ)) / (ramw v : ℝ) = 0
  rw [toy_vw_one]
  simp

theorem example_y_eq : (exampleObject K v0 Tw0).y = 1 / 2048 := by
  show (1 : ℝ) / (4 * ((8 : ℝ) * 1) ^ 3) = 1 / 2048
  norm_num

theorem example_depth_zero_eq_one (j : Unit) : (exampleObject K v0 Tw0).d0 j = 1 := by
  unfold OnObj.d0
  rw [example_eigenspace_eq_top, finrank_top, Module.finrank_fin_fun]
  show ((1 : ℕ) : ℝ) = 1
  norm_num

theorem example_aE_at_three_eq_zero : (exampleObject K v0 Tw0).aE () 3 = 0 := by
  show (1 : ℝ) * (Real.log 1 * 1 * 0 + 8 * 1 * (0 + 0)) / ((3 : ℕ) : ℝ) + 1 * 1 * 0 * 0 + 0 * 0 +
    (if (1 : ℝ) < ((3 : ℕ) : ℝ) then 1 * 1 * 0 / ((3 : ℕ) : ℝ) ^ 2 else 0) = 0
  simp

theorem example_error_at_three_eq_two : (exampleObject K v0 Tw0).errP () 3 = 2 := by
  unfold OnObj.errP
  rw [if_neg (show ¬((3 : ℕ) = (exampleObject K v0 Tw0).g1 ∨ (3 : ℕ) = (exampleObject K v0 Tw0).g2) from
      (by decide : ¬((3 : ℕ) = 5 ∨ (3 : ℕ) = 7))),
    if_neg (show (3 : ℕ) ∉ (exampleObject K v0 Tw0).sm from (by decide : (3 : ℕ) ∉ ({2} : Finset ℕ))),
    if_neg (show ¬((3 : ℕ) = (exampleObject K v0 Tw0).q1 ∨ (3 : ℕ) = (exampleObject K v0 Tw0).dd) from
      (by decide : ¬((3 : ℕ) = 11 ∨ (3 : ℕ) = 13)))]
  have hY3 : ((3 : ℕ) : ℝ) ≤ (exampleObject K v0 Tw0).Y := by
    show ((3 : ℕ) : ℝ) ≤ 1 * 3
    norm_num
  unfold errGood
  rw [if_pos hY3]
  have h := example_aE_at_three_eq_zero v0 Tw0
  unfold OnObj.aE at h
  rw [h]
  norm_num

theorem example_errOn_eq_two (w : HeightOneSpectrum (𝓞 K)) (hw : plc w = 3) (j : Unit) : (exampleObject K v0 Tw0).errOn w j = 2 := by
  cases j
  unfold OnObj.errOn OnObj.errl
  rw [hw, example_r_eq_zero, example_r_eq_zero, example_error_at_three_eq_two]
  simp

theorem example_mackey_condition : LeafMackey (exampleObject K v0 Tw0) := by
  exact ⟨rfl, fun _ _ _ _ => (one_mul 1).symm, fun h hh => absurd (Subgroup.mem_top h) hh⟩

theorem example_sup_condition : LeafSup (exampleObject K v0 Tw0) := by
  intro j
  refine ⟨stdLat_isLatIn K 1, fun g => le_of_eq ?_⟩
  exact map_id' K _

theorem example_projection_condition : LeafProj (exampleObject K v0 Tw0) := by
  intro j
  exact ⟨LinearMap.id_comp _, LinearMap.range_id⟩

theorem example_T_identity (w : HeightOneSpectrum (𝓞 K)) (t : Bool) (j : Unit) : (exampleObject K v0 Tw0).TjId j w t := by
  unfold OnObj.TjId OnObj.ImageLattice
  have h1 : ∀ A : Submodule (𝓞 K) (Fin 1 → K),
      A.map ((LinearMap.id : (Fin 1 → K) →ₗ[K] (Fin 1 → K)).restrictScalars (𝓞 K)) = A := fun A => map_id' K A
  show (matLat (1 : Matrix (Fin 1) (Fin 1) K) (stdLat K 1)).map
      ((LinearMap.id : (Fin 1 → K) →ₗ[K] (Fin 1 → K)).restrictScalars (𝓞 K)) =
    (((stdLat K 1).map ((LinearMap.id : (Fin 1 → K) →ₗ[K] (Fin 1 → K)).restrictScalars (𝓞 K))).map
      ((LinearMap.id : (Fin 1 → K) →ₗ[K] (Fin 1 → K)).restrictScalars (𝓞 K))).map
      ((LinearMap.id : (Fin 1 → K) →ₗ[K] (Fin 1 → K)).restrictScalars (𝓞 K))
  simp only [matLat_one', h1]

theorem example_coordinate_compatibility : TieCoord (exampleObject K v0 Tw0) := by
  refine ⟨fun j => ⟨fun _ _ h => h, ?_, ?_⟩, fun w _ j => ⟨example_T_identity v0 Tw0 _ _ j, example_T_identity v0 Tw0 _ _ j⟩⟩
  · rw [example_Zg_eq_top]
    exact LinearMap.range_id
  · rw [example_Zg_eq_top, cut_top']
    exact map_id' K _

theorem example_row_rank_condition : RankRows (exampleIndefiniteData K v0 Tw0 0) := by
  exact ⟨Nat.one_pos, fun _ => rfl⟩

theorem example_span_condition : LeafSpan (exampleObject K v0 Tw0) := by
  intro w _
  exact ⟨fun _ => ⟨stdLat_isLatIn K 1, stdLat_isLatIn K 1⟩, fun _ => ⟨stdLat_isLatIn K 1, stdLat_isLatIn K 1⟩⟩

theorem example_stable_lattice_condition : LeafLemmaS (exampleObject K v0 Tw0) := by
  have key : ∀ (v : HeightOneSpectrum (𝓞 K)) (j : Unit), (exampleObject K v0 Tw0).Th v j ≤ (exampleObject K v0 Tw0).Ms j ∧
      (∀ g : Unit, ((exampleObject K v0 Tw0).Th v j).map (((exampleObject K v0 Tw0).ρ j g).restrictScalars (𝓞 K)) ≤
        (exampleObject K v0 Tw0).Th v j) ∧
      (exampleObject K v0 Tw0).σ v j ≠ 0 ∧ (exampleObject K v0 Tw0).Th v j ≤ sc ((exampleObject K v0 Tw0).σ v j) ((exampleObject K v0 Tw0).ThK v j) :=
    fun v j => ⟨le_rfl, fun g => le_of_eq (map_id' K _), one_ne_zero, le_of_eq (sc_one' K _).symm⟩
  intro w _
  exact ⟨key w, key (conjPl w)⟩

theorem example_theorem_zero_condition : LatticeIndexBoundAtPairs (exampleObject K v0 Tw0) := by
  have h : ∀ (v : HeightOneSpectrum (𝓞 K)) (j : Unit),
      IsLatIn ⊤ ((exampleObject K v0 Tw0).Th1 v j) ∧ (exampleObject K v0 Tw0).Th1 v j ≤ (exampleObject K v0 Tw0).Th v j ∧
      (exampleObject K v0 Tw0).a v j ≠ 0 ∧ vw v ((exampleObject K v0 Tw0).a v j) = ((exampleObject K v0 Tw0).E v j : ℤ) ∧
      ∀ W : Submodule K (Fin ((exampleObject K v0 Tw0).nZ j) → K),
        (lix v (cut W ((exampleObject K v0 Tw0).Ms j)) (cut W ((exampleObject K v0 Tw0).Th1 v j)) : ℝ) ≤
          ((exampleObject K v0 Tw0).E v j : ℝ) * (finrank K W : ℝ) + (exampleObject K v0 Tw0).r v j := by
    intro v j
    refine ⟨stdLat_isLatIn K 1, le_rfl, one_ne_zero, toy_vw_one v, fun W => ?_⟩
    rw [example_r_eq_zero]
    show (lix v (cut W (stdLat K 1)) (cut W (stdLat K 1)) : ℝ) ≤ ((0 : ℕ) : ℝ) * (finrank K W : ℝ) + 0
    simp [lix, Formalism.HermitianLatticesTheory.lidx]
  have hb := example_b_ge v0 Tw0
  refine ⟨fun w _ => ⟨h w, h (conjPl w)⟩, by norm_num, le_rfl, fun _ _ => ⟨le_rfl, le_rfl⟩, fun _ S' => ?_⟩
  show ∑ v ∈ S', lw v * (0 : ℝ) ≤ ((1 : ℕ) : ℝ) * (8 * 1 * (exampleObject K v0 Tw0).b * 1) ∧
    ∑ v ∈ S', lw v * (0 : ℝ) ≤ ((1 : ℕ) : ℝ) * (8 * 1 * (exampleObject K v0 Tw0).b * 1)
  simp only [mul_zero, Finset.sum_const_zero, Nat.cast_one]
  constructor <;> linarith

theorem example_lattice_condition : LeafData (exampleObject K v0 Tw0) := by
  have key : ∀ (v : HeightOneSpectrum (𝓞 K)) (j : Unit), ((exampleObject K v0 Tw0).Th0 v j).FG ∧
      (exampleObject K v0 Tw0).Th0 v j ≤
        (eig ((exampleObject K v0 Tw0).ρ j) (exampleObject K v0 Tw0).U (exampleObject K v0 Tw0).ψ).restrictScalars (𝓞 K) ∧
      sc ((Nat.card (exampleObject K v0 Tw0).U : ℕ) : K) (cut (eig ((exampleObject K v0 Tw0).ρ j) (exampleObject K v0 Tw0).U (exampleObject K v0 Tw0).ψ)
        ((exampleObject K v0 Tw0).ThK v j)) ≤ (exampleObject K v0 Tw0).Th0 v j := by
    intro v j
    refine ⟨Submodule.fg_span (Set.finite_range _), ?_, le_of_eq ?_⟩
    · rw [example_eigenspace_eq_top, Submodule.restrictScalars_top]
      exact le_top
    · rw [example_eigenspace_eq_top, cut_top', show (exampleObject K v0 Tw0).U = ⊤ from rfl, toy_card, Nat.cast_one, sc_one']
  intro w _
  exact ⟨key w, key (conjPl w)⟩

theorem example_rank_condition : LeafRankJ (exampleObject K v0 Tw0) := by
  have key : ∀ (v : HeightOneSpectrum (𝓞 K)) (j : Unit),
      IsLatIn ((exampleObject K v0 Tw0).Zg j) (((exampleObject K v0 Tw0).Th0 v j).map (((exampleObject K v0 Tw0).e j).restrictScalars (𝓞 K))) ∧
      IsLatIn ((exampleObject K v0 Tw0).Zg j) ((exampleObject K v0 Tw0).eJ v j) ∧ (exampleObject K v0 Tw0).Th0 v j ≤ (exampleObject K v0 Tw0).ThJ v j := by
    intro v j
    rw [example_Zg_eq_top,
      show ((exampleObject K v0 Tw0).Th0 v j).map (((exampleObject K v0 Tw0).e j).restrictScalars (𝓞 K)) = stdLat K 1 from map_id' K _,
      show (exampleObject K v0 Tw0).eJ v j = stdLat K 1 from map_id' K _]
    exact ⟨stdLat_isLatIn K 1, stdLat_isLatIn K 1, le_rfl⟩
  intro w _
  exact ⟨key w, key (conjPl w)⟩

theorem example_identity_condition : LeafIdentity (exampleObject K v0 Tw0) := by
  intro w _
  exact ⟨fun j => ⟨rfl, fun x _ => by rw [LinearMap.mem_ker]; exact sub_self x⟩,
    fun j => ⟨rfl, fun x _ => by rw [LinearMap.mem_ker]; exact sub_self x⟩⟩

theorem example_second_twist_condition : LeafTW2 (exampleObject K v0 Tw0) := by
  have key : ∀ (v : HeightOneSpectrum (𝓞 K)) (j : Unit), IsLatIn ((exampleObject K v0 Tw0).Zg j) ((exampleObject K v0 Tw0).X₃ v j) ∧
      IsLatIn ((exampleObject K v0 Tw0).Zg j) ((exampleObject K v0 Tw0).Im v j) ∧
      Formalism.HermitianLatticesTheory.localization₂ v.asIdeal ((exampleObject K v0 Tw0).X₃ v j) ≤ Formalism.HermitianLatticesTheory.localization₂ v.asIdeal ((exampleObject K v0 Tw0).Im v j) := by
    intro v j
    have hIm : (exampleObject K v0 Tw0).Im v j = stdLat K 1 := by
      unfold OnObj.Im
      rw [show ((exampleObject K v0 Tw0).Mt v j).map (((exampleObject K v0 Tw0).θ' v j).restrictScalars (𝓞 K)) = stdLat K 1
        from map_id' K _]
      exact map_id' K _
    rw [example_Zg_eq_top, hIm]
    exact ⟨stdLat_isLatIn K 1, stdLat_isLatIn K 1, le_rfl⟩
  intro w _
  exact ⟨key w, key (conjPl w)⟩

theorem example_first_twist_condition : LeafTW1 (exampleObject K v0 Tw0) := by
  have hz : ∀ (v : HeightOneSpectrum (𝓞 K)) (j : Unit),
      (lix v (cut ((exampleObject K v0 Tw0).Zg j) ((exampleObject K v0 Tw0).Ms j)) ((exampleObject K v0 Tw0).X₃ v j) : ℝ) ≤
        (lix v (cut ((exampleObject K v0 Tw0).Zg j) ((exampleObject K v0 Tw0).Ms j)) ((exampleObject K v0 Tw0).eJ v j) : ℝ) +
          (ramw v : ℝ) * (exampleObject K v0 Tw0).ε0 v j := by
    intro v j
    rw [show (exampleObject K v0 Tw0).eJ v j = stdLat K 1 from map_id' K _]
    show _ ≤ _ + (ramw v : ℝ) * 0
    rw [mul_zero, add_zero]
  refine ⟨fun w _ => ⟨fun j => ⟨le_rfl, hz w j⟩, fun j => ⟨le_rfl, hz (conjPl w) j⟩⟩, fun w _ => ?_⟩
  show ∑ j : Unit, ((0 : ℝ) + 0) ≤ 2 / ((plc w : ℕ) : ℝ) ^ 2
  simp only [add_zero, Finset.sum_const_zero]
  positivity

theorem example_share_condition : LeafShareI (exampleObject K v0 Tw0) := by
  intro j
  refine ⟨0, ?_, ?_⟩
  · rw [example_y_eq]
    norm_num
  · rw [example_depth_zero_eq_one, show (exampleObject K v0 Tw0).U = ⊤ from rfl, toy_card]
    show (1 - 0) * ((1 : ℕ) : ℝ) ≤ ((1 : ℕ) : ℝ) * 1
    norm_num

theorem example_index_condition : LeafIndexU (exampleObject K v0 Tw0) := by
  unfold LeafIndexU
  rw [example_y_eq, show (exampleObject K v0 Tw0).U = ⊤ from rfl, toy_card, Subgroup.index_top]
  norm_num

theorem example_bad_share_condition : LeafBadShare (exampleObject K v0 Tw0) := by
  intro j
  refine ⟨0, le_rfl, by norm_num, ?_⟩
  rw [example_depth_zero_eq_one]
  show (1 - 0) * (1 : ℝ) ≤ ((1 : ℕ) : ℝ)
  norm_num

theorem example_unipotent_condition : LeafUnip (exampleObject K v0 Tw0) := by
  refine ⟨le_rfl, fun w _ => ?_⟩
  rw [show (exampleObject K v0 Tw0).U = ⊤ from rfl, toy_card, Nat.cast_one, toy_vw_one]
  split_ifs
  · show ((0 : ℤ) : ℝ) = (ramw w : ℝ) * (8 * 1 * (1 - 1) / 2)
    norm_num
  · norm_num

variable (h3 : ∀ w ∈ Tw0, plc w = 3)
include h3

theorem example_depth_condition_good (F E : ℝ) (hF : -1 ≤ F) : LeafDepthGood (exampleConstants K v0 F E) (exampleObject K v0 Tw0) := by
  have hY : (exampleObject K v0 Tw0).Y = 3 := by
    show (1 : ℝ) * 3 = 3
    norm_num
  refine ⟨fun _ => ⟨le_rfl, le_rfl⟩, fun Q _ => ?_, fun Q _ => ?_, ?_⟩
  · show ∑ p ∈ Q, (0 : ℝ) * Real.log (p : ℝ) ≤ 1 / 1
    simp
  · show (0 : ℝ) * ∑ p ∈ Q, (0 : ℝ) * Real.log (p : ℝ) ≤ 1 * (1 * (exampleObject K v0 Tw0).b)
    rw [zero_mul]
    linarith [example_b_ge v0 Tw0]
  · intro w hw _ j
    cases j
    have hp := h3 w hw
    have hF0 : (exampleConstants K v0 F E).F0 w () = F := by
      show (if plc w = 3 then F else 0) = F
      rw [if_pos hp]
    refine ⟨fun _ => ?_, fun hlt => ?_⟩
    · rw [example_ramification_zero, example_ramification_zero, hF0, hp, example_aE_at_three_eq_zero]
      constructor <;> linarith
    · exfalso
      rw [hY, hp] at hlt
      norm_num at hlt

theorem example_depth_condition_ramified (F E : ℝ) : LeafDepthRam (exampleConstants K v0 F E) (exampleObject K v0 Tw0) := by
  intro w hw hq j
  exfalso
  have h : plc w = 11 ∨ plc w = 13 := hq
  rw [h3 w hw] at h
  omega

theorem example_depth_condition_dyadic (F E : ℝ) : LeafDepth2 (exampleConstants K v0 F E) (exampleObject K v0 Tw0) := by
  intro w hw hs j
  exfalso
  have h : plc w ∈ ({2} : Finset ℕ) := hs
  rw [h3 w hw, Finset.mem_singleton] at h
  omega

theorem example_depth_condition_level (F E : ℝ) : LeafDepthLevel (exampleConstants K v0 F E) (exampleObject K v0 Tw0) := by
  intro w hw hg j
  exfalso
  have h : plc w = 5 ∨ plc w = 7 := hg
  rw [h3 w hw] at h
  omega

omit h3

theorem example_numerical_condition : LeafPage (exampleObject K v0 Tw0) := by
  unfold LeafPage
  norm_num [exampleObject, exampleC, OnObj.C]

theorem example_size_condition₂ : LeafSizes (exampleObject K v0 Tw0) := by
  have hY : (exampleObject K v0 Tw0).Y = 3 := by
    show (1 : ℝ) * 3 = 3
    norm_num
  have hb := example_b_ge v0 Tw0
  refine ⟨fun j => ⟨le_rfl, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · show (0 : ℝ) ≤ 2 * 8 * (exampleObject K v0 Tw0).b
    linarith
  · rw [hY]
    norm_num
  · rw [hY, example_L_eq]
    have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 3)
    linarith
  · rw [hY]
    show (3 : ℝ) ≤ 1 * (exampleObject K v0 Tw0).b
    linarith
  · show (1 : ℝ) * (0 + 0) * (exampleObject K v0 Tw0).L ≤ 1 * (exampleObject K v0 Tw0).b
    rw [example_L_eq]
    linarith
  · show (1 : ℝ) ≤ 1
    exact le_rfl
  · show Real.log 1 ≤ (exampleObject K v0 Tw0).L
    rw [Real.log_one, example_L_eq]
    norm_num
  · rw [example_L_eq]
    norm_num

theorem example_size_condition : LeafX (exampleObject K v0 Tw0) := by
  refine ⟨?_, ?_⟩
  · rw [example_xe_eq]
    show Real.log 300 ≤ 300
    have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 300)
    linarith
  · show ((0 : ℕ) : ℝ) ≤ 8
    norm_num

theorem example_bad_primes_condition : LeafBad (exampleObject K v0 Tw0) := by
  have hb := example_b_ge v0 Tw0
  refine ⟨?_, ?_, fun j => ⟨?_, ?_, ?_⟩⟩
  · show (0 : ℝ) ≤ 2 * Real.log 143
    have := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 143)
    linarith
  · show (0 : ℝ) ≤ 1
    norm_num
  · show (2 * ((0 : ℝ) + 8 * (0 + 0) + 0 + 1) + 4 * (8 * 1 * 0)) * Real.log ((11 * 13 : ℕ) : ℝ) ≤
      2 * Real.log 143 * (8 * 1 * (exampleObject K v0 Tw0).b)
    have h143 : ((11 * 13 : ℕ) : ℝ) = 143 := by norm_num
    rw [h143]
    have := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 143)
    nlinarith
  · show (∑ p ∈ ({2} : Finset ℕ), Real.log (p : ℝ)) * (2 * (1 * 1 * (2 + 0) * (0 + 8 * (0 + 0))) + 2 * 0 + 2) ≤
      1 * (8 * 1 * (exampleObject K v0 Tw0).b * (exampleObject K v0 Tw0).L)
    rw [Finset.sum_singleton, example_L_eq]
    have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    push_cast
    nlinarith
  · show (4 * (0 : ℝ) + 4 * 8 * 1 ^ 2) * Real.log ((5 * 7 : ℕ) : ℝ) ≤ 4 * (exampleObject K v0 Tw0).b
    have h35 : ((5 * 7 : ℕ) : ℝ) = 35 := by norm_num
    rw [h35]
    have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 35)
    nlinarith

theorem example_j_sum_condition : LeafJSum (exampleObject K v0 Tw0) := by
  intro j
  refine ⟨fun _ => le_rfl, fun Q _ => ?_⟩
  show ∑ p ∈ Q, (0 : ℝ) * Real.log (p : ℝ) ≤
    30 * ((0 : ℕ) : ℝ) * 1 * (exampleObject K v0 Tw0).b * (exampleObject K v0 Tw0).xe ^ 2 + 2 * 1 * (exampleObject K v0 Tw0).b
  simp only [zero_mul, Finset.sum_const_zero, Nat.cast_zero, mul_zero, zero_add]
  linarith [example_b_ge v0 Tw0]

theorem example_j_exponent_condition (F E : ℝ) : LeafJExp (exampleConstants K v0 F E) (exampleObject K v0 Tw0) := by
  exact fun _ _ _ => le_rfl

theorem example_error_constant_matches (F : ℝ) :
    ErrorConstantMatchesDefinition (exampleConstants K v0 F (exampleC.CE * (exampleObject K v0 Tw0).E1u)) (exampleObject K v0 Tw0) exampleC.CE := by
  exact fun _ => rfl

theorem example_ON (h3 : ∀ w ∈ Tw0, plc w = 3) :
    ({ exampleIndefiniteData K v0 Tw0 0 with err0 := (exampleObject K v0 Tw0).errOn } : IndefData (exampleDf K v0)).ON
      (exampleConstants K v0 1 (exampleC.CE * (exampleObject K v0 Tw0).E1u)) := by
  exact on_built (exampleConstants K v0 1 (exampleC.CE * (exampleObject K v0 Tw0).E1u)) (exampleObject K v0 Tw0) exampleC.CE (example_row_rank_condition v0 Tw0)
    (example_mackey_condition v0 Tw0) (example_sup_condition v0 Tw0) (example_projection_condition v0 Tw0) (example_coordinate_compatibility v0 Tw0) (example_span_condition v0 Tw0) (example_stable_lattice_condition v0 Tw0)
    (example_theorem_zero_condition v0 Tw0) (example_lattice_condition v0 Tw0) (example_rank_condition v0 Tw0) (example_identity_condition v0 Tw0) (example_second_twist_condition v0 Tw0) (example_first_twist_condition v0 Tw0)
    (example_share_condition v0 Tw0) (example_index_condition v0 Tw0) (example_bad_share_condition v0 Tw0) (example_unipotent_condition v0 Tw0)
    (example_depth_condition_good v0 Tw0 h3 1 _ (by norm_num)) (example_depth_condition_ramified v0 Tw0 h3 1 _) (example_depth_condition_dyadic v0 Tw0 h3 1 _)
    (example_depth_condition_level v0 Tw0 h3 1 _) (example_numerical_condition v0 Tw0) (example_size_condition₂ v0 Tw0) (example_size_condition v0 Tw0) (example_bad_primes_condition v0 Tw0)
    (example_j_sum_condition v0 Tw0) (example_j_exponent_condition v0 Tw0 1 _) le_rfl (example_error_constant_matches v0 Tw0 1)

theorem example_nondegenerate_at_three (w : HeightOneSpectrum (𝓞 K)) (hw : plc w = 3) :
    (exampleObject K v0 Tw0).errOn w () = 2 ∧ (exampleConstants K v0 1 0).F0 w () = 1 ∧ ((plc w : ℝ) ≤ (exampleObject K v0 Tw0).Y) ∧
      (exampleObject K v0 Tw0).Bad = {5, 7, 11, 13, 2} := by
  refine ⟨example_errOn_eq_two v0 Tw0 w hw (), ?_, ?_, rfl⟩
  · show (if plc w = 3 then (1 : ℝ) else 0) = 1
    rw [if_pos hw]
  · rw [hw]
    show ((3 : ℕ) : ℝ) ≤ 1 * 3
    norm_num

theorem example_fails_at_three (w0 : HeightOneSpectrum (𝓞 K)) (h3w : plc w0 = 3) (E : ℝ) (hE : E < 2 * (lw w0 * (ramw w0 : ℝ))) :
    ¬ ({ exampleIndefiniteData K v0 {w0} 0 with err0 := (exampleObject K v0 {w0}).errOn } : IndefData (exampleDf K v0)).ON (exampleConstants K v0 1 E) := by
  intro h
  have h3 := h.2.2 ()
  have he : (exampleObject K v0 {w0}).errOn w0 () = 2 := example_errOn_eq_two v0 {w0} w0 h3w ()
  change ∑ w ∈ ({w0} : Finset (HeightOneSpectrum (𝓞 K))),
      lw w * ((ramw w : ℝ) * (exampleObject K v0 {w0}).errOn w () + (ramw w : ℝ) * 0) ≤ E at h3
  rw [Finset.sum_singleton, he] at h3
  linarith

theorem example_negative_content_fails (w0 : HeightOneSpectrum (𝓞 K)) (h3w : plc w0 = 3) (E : ℝ) :
    ¬ LeafDepthGood (exampleConstants K v0 (-10) E) (exampleObject K v0 {w0}) ∧
    ¬ ({ exampleIndefiniteData K v0 {w0} 0 with err0 := (exampleObject K v0 {w0}).errOn } : IndefData (exampleDf K v0)).ON (exampleConstants K v0 (-10) E) := by
  have hY : ((plc w0 : ℕ) : ℝ) ≤ (exampleObject K v0 {w0}).Y := by
    rw [h3w]
    show ((3 : ℕ) : ℝ) ≤ 1 * 3
    norm_num
  have hF : (exampleConstants K v0 (-10) E).F0 w0 () = -10 := by
    show (if plc w0 = 3 then (-10 : ℝ) else 0) = -10
    rw [if_pos h3w]
  refine ⟨fun h => ?_, fun h => ?_⟩
  · have hn : ¬ (plc w0 ∈ (exampleObject K v0 {w0}).sm ∨ plc w0 = (exampleObject K v0 {w0}).q1 ∨ plc w0 = (exampleObject K v0 {w0}).dd ∨
        plc w0 = (exampleObject K v0 {w0}).g1 ∨ plc w0 = (exampleObject K v0 {w0}).g2) := by
      rw [h3w]
      exact (by decide : ¬ ((3 : ℕ) ∈ ({2} : Finset ℕ) ∨ (3 : ℕ) = 11 ∨ (3 : ℕ) = 13 ∨ (3 : ℕ) = 5 ∨ (3 : ℕ) = 7))
    have h1 := ((h.2.2.2 w0 (Finset.mem_singleton_self w0) hn ()).1 hY).1
    rw [example_ramification_zero, h3w, example_aE_at_three_eq_zero, hF] at h1
    linarith
  · have h1 := h.1 w0 (Finset.mem_singleton_self w0)
    have he : (exampleObject K v0 {w0}).errOn w0 () = 2 := example_errOn_eq_two v0 {w0} w0 h3w ()
    have hI : ∀ w : HeightOneSpectrum (𝓞 K), (idx w (stdLat K 1) (matLat (1 : Matrix (Fin 1) (Fin 1) K) (stdLat K 1)) : ℝ) = 0 := by
      intro w
      rw [matLat_one']
      unfold idx Formalism.HermitianLatticesTheory.lidx
      simp
    change ∑ j : Unit, ((idx w0 (stdLat K 1) (matLat (1 : Matrix (Fin 1) (Fin 1) K) (stdLat K 1)) : ℝ) +
        (idx (conjPl w0) (stdLat K 1) (matLat (1 : Matrix (Fin 1) (Fin 1) K) (stdLat K 1)) : ℝ)) ≤
      (∑ j : Unit, (2 * ((ramw w0 : ℝ) * (exampleConstants K v0 (-10) E).F0 w0 j) + (ramw w0 : ℝ) * (exampleObject K v0 {w0}).errOn w0 j) +
        (ramw w0 : ℝ) * (2 / (plc w0 : ℝ) ^ 2)) * ((1 : ℕ) : ℝ) at h1
    simp only [Fintype.univ_unit, Finset.sum_singleton, hI, hF, he, h3w] at h1
    have hr := ramw_pos w0
    push_cast at h1
    nlinarith

theorem depth_free_fails (w0 : HeightOneSpectrum (𝓞 K)) (h3w : plc w0 = 3) (E : ℝ) :
    ¬ LeafDepthGood (exampleConstants K v0 (-10) E) (exampleObject K v0 {w0}) := by
  intro h
  have hn : ¬ (plc w0 ∈ (exampleObject K v0 {w0}).sm ∨ plc w0 = (exampleObject K v0 {w0}).q1 ∨ plc w0 = (exampleObject K v0 {w0}).dd ∨
      plc w0 = (exampleObject K v0 {w0}).g1 ∨ plc w0 = (exampleObject K v0 {w0}).g2) := by
    rw [h3w]
    exact (by decide : ¬ ((3 : ℕ) ∈ ({2} : Finset ℕ) ∨ (3 : ℕ) = 11 ∨ (3 : ℕ) = 13 ∨ (3 : ℕ) = 5 ∨ (3 : ℕ) = 7))
  have hY : ((plc w0 : ℕ) : ℝ) ≤ (exampleObject K v0 {w0}).Y := by
    rw [h3w]
    show ((3 : ℕ) : ℝ) ≤ 1 * 3
    norm_num
  have h1 := ((h.2.2.2 w0 (Finset.mem_singleton_self w0) hn ()).1 hY).1
  rw [example_ramification_zero, h3w, example_aE_at_three_eq_zero] at h1
  have hF : (exampleConstants K v0 (-10) E).F0 w0 () = -10 := by
    show (if plc w0 = 3 then (-10 : ℝ) else 0) = -10
    rw [if_pos h3w]
  rw [hF] at h1
  linarith

theorem lw_pos (w : HeightOneSpectrum (𝓞 K)) : 0 < lw w := by
  unfold lw
  have h1 : Ideal.absNorm w.asIdeal ≠ 1 := fun h => w.isPrime.ne_top (Ideal.absNorm_eq_one_iff.mp h)
  have h0 : Ideal.absNorm w.asIdeal ≠ 0 := fun h => w.ne_bot (Ideal.absNorm_eq_zero_iff.mp h)
  have h2 : (1 : ℝ) < (Ideal.absNorm w.asIdeal : ℝ) := by
    have h3 : 1 < Ideal.absNorm w.asIdeal := by omega
    exact_mod_cast h3
  apply div_pos (Real.log_pos h2)
  have h4 : 0 < finrank ℚ K := Module.finrank_pos
  exact_mod_cast h4

theorem theorem_zero_condition_not_automatic (w0 : HeightOneSpectrum (𝓞 K)) :
    ¬ LatticeIndexBoundAtPairs ({ exampleObject K v0 {w0} with r1 := fun _ _ => (8 * Real.exp 300 + 1) / lw w0 } : OnObj (exampleIndefiniteData K v0 {w0} 0) Unit exampleC) := by
  intro h
  have h1 := (h.2.2.2.2 () {w0}).1
  rw [Finset.sum_singleton] at h1
  have hl := lw_pos w0
  change lw w0 * ((8 * Real.exp 300 + 1) / lw w0) ≤ ((1 : ℕ) : ℝ) * (8 * 1 * Real.exp ((300 : ℝ) ^ (1 : ℝ)) * 1) at h1
  have e : lw w0 * ((8 * Real.exp 300 + 1) / lw w0) = 8 * Real.exp 300 + 1 := by
    field_simp
  rw [e, Real.rpow_one] at h1
  push_cast at h1
  linarith

theorem example_fails_at_three_nonneg_error (w0 : HeightOneSpectrum (𝓞 K)) (h3w : plc w0 = 3) :
    0 ≤ lw w0 * (ramw w0 : ℝ) ∧
    ¬ ({ exampleIndefiniteData K v0 {w0} 0 with err0 := (exampleObject K v0 {w0}).errOn } : IndefData (exampleDf K v0)).ON
      (exampleConstants K v0 1 (lw w0 * (ramw w0 : ℝ))) := by
  refine ⟨mul_nonneg (lw_pos w0).le (ramw_pos w0).le, example_fails_at_three v0 w0 h3w _ ?_⟩
  have := mul_pos (lw_pos w0) (ramw_pos w0)
  linarith

theorem exists_place_prime (p : ℕ) (hp : p.Prime) : ∃ w : HeightOneSpectrum (𝓞 K), plc w = p := by
  exact exists_place_lemma K p hp

section Level

variable (h5 : ∀ w ∈ Tw0, plc w = 5)
include h5

theorem example_good_depth_condition (F E : ℝ) : LeafDepthGood (exampleConstants K v0 F E) (exampleObject K v0 Tw0) := by
  refine ⟨fun _ => ⟨le_rfl, le_rfl⟩, fun Q _ => ?_, fun Q _ => ?_, ?_⟩
  · show ∑ p ∈ Q, (0 : ℝ) * Real.log (p : ℝ) ≤ 1 / 1
    simp
  · show (0 : ℝ) * ∑ p ∈ Q, (0 : ℝ) * Real.log (p : ℝ) ≤ 1 * (1 * (exampleObject K v0 Tw0).b)
    rw [zero_mul]
    linarith [example_b_ge v0 Tw0]
  · intro w hw hn j
    exfalso
    exact hn (Or.inr (Or.inr (Or.inr (Or.inl (h5 w hw)))))

theorem example_ramified_depth_condition (F E : ℝ) : LeafDepthRam (exampleConstants K v0 F E) (exampleObject K v0 Tw0) := by
  intro w hw hq j
  exfalso
  have h : plc w = 11 ∨ plc w = 13 := hq
  rw [h5 w hw] at h
  omega

theorem example_depth_two_condition (F E : ℝ) : LeafDepth2 (exampleConstants K v0 F E) (exampleObject K v0 Tw0) := by
  intro w hw hs j
  exfalso
  have h : plc w ∈ ({2} : Finset ℕ) := hs
  rw [h5 w hw, Finset.mem_singleton] at h
  omega

theorem example_level_depth_condition (F E : ℝ) : LeafDepthLevel (exampleConstants K v0 F E) (exampleObject K v0 Tw0) := by
  intro w hw _ j
  have hnn : ∀ v, (exampleObject K v0 Tw0).nn v j = 0 := by
    intro v
    show ((vw v (1 : K) : ℤ) : ℝ) / (ramw v : ℝ) = 0
    rw [toy_vw_one]
    simp
  have hF0 : (exampleConstants K v0 F E).F0 w j = 0 := by
    show (if plc w = 3 then F else 0) = 0
    rw [if_neg (by rw [h5 w hw]; norm_num)]
  rw [example_ramification_zero, example_ramification_zero, hnn, hnn, hF0]
  show (0 : ℝ) ≤ 2 * 0 - 0 ∧ (0 : ℝ) ≤ 2 * 0 - 0 ∧ (0 : ℝ) + 0 = -(2 * 0)
  norm_num

theorem example_satisfies_conditions_at_five :
    ({ exampleIndefiniteData K v0 Tw0 0 with err0 := (exampleObject K v0 Tw0).errOn } : IndefData (exampleDf K v0)).ON
      (exampleConstants K v0 1 (exampleC.CE * (exampleObject K v0 Tw0).E1u)) := by
  exact on_built (exampleConstants K v0 1 (exampleC.CE * (exampleObject K v0 Tw0).E1u)) (exampleObject K v0 Tw0) exampleC.CE (example_row_rank_condition v0 Tw0)
    (example_mackey_condition v0 Tw0) (example_sup_condition v0 Tw0) (example_projection_condition v0 Tw0) (example_coordinate_compatibility v0 Tw0) (example_span_condition v0 Tw0) (example_stable_lattice_condition v0 Tw0)
    (example_theorem_zero_condition v0 Tw0) (example_lattice_condition v0 Tw0) (example_rank_condition v0 Tw0) (example_identity_condition v0 Tw0) (example_second_twist_condition v0 Tw0) (example_first_twist_condition v0 Tw0)
    (example_share_condition v0 Tw0) (example_index_condition v0 Tw0) (example_bad_share_condition v0 Tw0) (example_unipotent_condition v0 Tw0)
    (example_good_depth_condition v0 Tw0 h5 1 _) (example_ramified_depth_condition v0 Tw0 h5 1 _) (example_depth_two_condition v0 Tw0 h5 1 _)
    (example_level_depth_condition v0 Tw0 h5 1 _) (example_numerical_condition v0 Tw0) (example_size_condition₂ v0 Tw0) (example_size_condition v0 Tw0) (example_bad_primes_condition v0 Tw0)
    (example_j_sum_condition v0 Tw0) (example_j_exponent_condition v0 Tw0 1 _) le_rfl (example_error_constant_matches v0 Tw0 1)

end Level

theorem example_error_at_five (w : HeightOneSpectrum (𝓞 K)) (hw : plc w = 5) (j : Unit) : (exampleObject K v0 Tw0).errOn w j = 32 := by
  cases j
  have he : (exampleObject K v0 Tw0).errP () 5 = 32 := by
    unfold OnObj.errP
    rw [if_pos (show (5 : ℕ) = (exampleObject K v0 Tw0).g1 ∨ (5 : ℕ) = (exampleObject K v0 Tw0).g2 from Or.inl rfl)]
    show 4 * (0 : ℝ) + 4 * 8 * 1 ^ 2 = 32
    norm_num
  unfold OnObj.errOn OnObj.errl
  rw [hw, example_r_eq_zero, example_r_eq_zero, he]
  simp

end Examples₂

end Formalism.L2.Indef.Tree
