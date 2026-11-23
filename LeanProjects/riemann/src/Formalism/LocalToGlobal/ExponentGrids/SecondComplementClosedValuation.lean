import Mathlib
import Formalism.LocalToGlobal.ExponentGrids.SecondComplementColumnExponents
import Formalism.SizeWindowBrackets.SlopesFromSizeAndCount
import Formalism.LocalRingCardinality.DataErr
import Formalism.LocalToGlobal.GlobalTheory.IsResidueClassZero

open Module NumberField IsDedekindDomain Finset
open Formalism.DivisionValues (vw conjPl PlOver)
open Formalism.CG (HCdeg HCDplus HCDminus)
open Formalism.D5 (PhiSet E0)
open Formalism.LFunctionChainParameters.characterSumData (ArithData)
open Formalism.RankGapBounds.WeightedMeanData (Consts)
open Formalism.LFunctionChainParameters Formalism.LFunctionChainParameters.WeightedSlopeBounds Formalism.LFunctionChainParameters.LChain2 Formalism.LFunctionChainParameters.LChain6
open Formalism.LFunctionChainParameters.LBrDiv (plOf TypePrimeCostDeviationBound)

noncomputable section

namespace Formalism.AtG

section Defs

variable {K : Type} [Field K] [NumberField K] {Pl : Type} [Fintype Pl]

def vNNg (g : ℕ) (p : Pl → K) (ν : Pl → ℝ) (w : HeightOneSpectrum (𝓞 K)) : ℝ :=
  (∑ ρ, ν ρ * (vw w (p ρ) : ℝ)) / (vw w (g : K) : ℝ)

def EGval (g : ℕ) (p : Pl → K) (ν : Pl → ℝ) (Dpm o : ℝ) (w : HeightOneSpectrum (𝓞 K)) : ℝ :=
  -(Dpm / 2) + vNNg g p ν w + o

end Defs

def oG (dG c f N m η : ℝ) : ℝ := dG + c * f * (N ^ 2 + m ^ 2 * η)

structure HarishChandraParameters (Pl : Type) where

  k : ℕ

  t : ℕ

  u : Pl → ℕ → ℚ

  v : Pl → ℕ → ℚ

  e : Pl → ℕ → ℚ
  bb : Pl → ℕ → ℚ

  a : Pl → ℚ
  bt : Pl → ℚ
  b0 : ℚ

  xq : ℚ
  S : ℚ
  η : ℚ
  C : ℚ
  N : ℝ
  w'' : ℝ
  X'' : ℝ
  logd : ℝ

namespace HarishChandraParameters

variable {Pl : Type} (P : HarishChandraParameters Pl)

def deg (j : ℕ) (ρ : Pl) : ℚ := HCdeg P.k P.t (P.u ρ) (P.e ρ) j

def Dpm [Fintype Pl] (m j : ℕ) : ℝ :=
  ((∑ ρ, (HCDplus P.k P.t m j (P.v ρ) (P.bb ρ) (P.e ρ) + HCDminus P.k P.t m j (P.v ρ) (P.bb ρ) (P.e ρ)) : ℚ) : ℝ)

end HarishChandraParameters

def ParameterSizeInequalities {Pl : Type} [Fintype Pl] (P : HarishChandraParameters Pl) (TT : Finset Pl) (m : ℕ) (x eps f b C0 lg : ℝ) : Prop :=
  HarishChandraParamConditions TT P.k P.t m P.u P.v P.e P.bb P.a P.bt P.b0 P.xq P.S P.η P.C ∧
  1 ≤ x ∧ x ≤ (P.xq : ℝ) ∧ 0 < eps ∧ 0 ≤ b ∧ (Fintype.card Pl : ℝ) ≤ f ∧ 1 ≤ m ∧ 1 ≤ f ∧ 1 ≤ P.N ∧ 0 ≤ P.logd ∧
  (∀ (j : Fin m) ρ, 0 ≤ (P.e ρ (j.val + 1) : ℝ) ∧ (P.e ρ (j.val + 1) : ℝ) ≤ 2 * b) ∧
  (P.k : ℝ) * P.S ≤ P.w'' ∧ (m : ℝ) * ((P.t : ℝ) + 1) * P.η ≤ P.w'' ∧ P.N * P.w'' ≤ b ∧ P.N * (P.N + P.t) ≤ b ∧
  (P.k : ℝ) * P.b0 ≤ b ∧ f * P.k * P.N * P.X'' ≤ b ∧ P.logd ≤ x ^ eps ∧ lg ≤ C0 * x ^ eps ∧ (P.C : ℝ) + 3 ≤ C0

def ErrorSizeConditions {Pl : Type} (P : HarishChandraParameters Pl) (TT : Finset Pl) (m : ℕ) (x eps f b C0 : ℝ) (o : Fin m → Fin 2 → ℝ)
    (Eels : Fin m → ℝ) : Prop :=
  (∀ j i, |o j i| ≤ C0 * (f * (P.N * (P.N + P.t) + (m : ℝ) ^ 2 * P.η))) ∧
  (∀ j, Eels j ≤ C0 * (f * m * b * x ^ eps) + ((TT.card : ℝ) * (2 * b + 4 * P.k * P.b0) + 4 * f * P.k * P.b0) * P.logd +
    C0 * (f * P.k * P.N * P.X''))

def ParameterSizesNonempty : Prop :=
  ∃ (P : HarishChandraParameters Bool) (TT : Finset Bool) (x eps f b C0 lg : ℝ) (o : Fin 2 → Fin 2 → ℝ) (Eels : Fin 2 → ℝ),
    true ∈ TT ∧ false ∉ TT ∧ 0 < lg ∧ (∀ j i, 0 < o j i) ∧ (∀ j, 0 < Eels j) ∧
    ParameterSizeInequalities P TT 2 x eps f b C0 lg ∧ ErrorSizeConditions P TT 2 x eps f b C0 o Eels

def PlacesOverPrimeCompatibility : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (g : ℕ), g.Prime → ∀ z : HeightOneSpectrum (𝓞 K),
    (PlOver g z ↔ prBelow (plOf z) = g) ∧ (PlOver g z → ramE (plOf z) = (vw z (g : K) : ℝ)) ∧
    LBrDiv.lw z = Formalism.DivisionValues.lw z ∧ lE (plOf z) = Formalism.DivisionValues.lw z * ramE (plOf z)

def PrimeIdealsFinitePlacesSum : Prop :=
  ∀ (K : Type) [Field K] [NumberField K],
    Function.Bijective (plOf : HeightOneSpectrum (𝓞 K) → slopeLatticeData.FinPl K) ∧
    ∀ (S : Finset (slopeLatticeData.FinPl K)) (f : slopeLatticeData.FinPl K → ℝ),
      (Function.support fun z : HeightOneSpectrum (𝓞 K) =>
        if plOf z ∈ S then ramE (plOf z) * f (plOf z) else 0).Finite ∧
      ∑ᶠ z : HeightOneSpectrum (𝓞 K), LBrDiv.lw z * (if plOf z ∈ S then ramE (plOf z) * f (plOf z) else 0)
        = ∑ w ∈ S, lE w * f w

def ValuationOfProductSum : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (Pl : Type) [Fintype Pl] (p : Pl → K), (∀ ρ, p ρ ≠ 0) →
    ∀ (D : Pl → ℕ) (w : HeightOneSpectrum (𝓞 K)),
      ∑ ρ, (D ρ : ℝ) * (vw w (p ρ) : ℝ) = (vw w (∏ ρ, p ρ ^ D ρ) : ℝ)

def ConjugatePlacePairSumIdentity : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (g : ℕ) (Pl : Type) [Fintype Pl] (p : Pl → K),
    (∀ ρ, p ρ * star (p ρ) = (g : K)) → ∀ (ν : Pl → ℝ) (Dpm o : ℝ) (w : HeightOneSpectrum (𝓞 K)), PlOver g w →
      vNNg g p ν w + vNNg g p ν (conjPl w) = ∑ ρ, ν ρ ∧
      EGval g p ν Dpm o w + EGval g p ν Dpm o (conjPl w) = ∑ ρ, ν ρ - Dpm + 2 * o

def NormaliserSeenAtOnePlace : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (g : ℕ) (Pl : Type) [Fintype Pl] (pb x y : K),
    pb * star pb = (g : K) → x * pb + y * star pb = 1 →
    ∀ (ν : Pl → ℝ) (w : HeightOneSpectrum (𝓞 K)), PlOver g w → 0 ≤ vw w x → 0 ≤ vw w y → 0 ≤ vw w pb →
    0 ≤ vw (conjPl w) pb →
      (vNNg g (fun _ : Pl => pb) ν w = 0 ∧ vNNg g (fun _ : Pl => pb) ν (conjPl w) = ∑ ρ, ν ρ) ∨
      (vNNg g (fun _ : Pl => pb) ν w = ∑ ρ, ν ρ ∧ vNNg g (fun _ : Pl => pb) ν (conjPl w) = 0)

def PlacesAbovePrimeSum : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K] (g : ℕ), 0 < g →
    ∀ (Pl : Type) [Fintype Pl] (p : Pl → K), (∀ ρ, p ρ * star (p ρ) = (g : K)) → ∀ (ν : Pl → ℝ) (Dpm o : ℝ),
      2 * (∑ᶠ (w : HeightOneSpectrum (𝓞 K)) (_ : PlOver g w),
        Formalism.DivisionValues.lw w * ((vw w (g : K) : ℝ) * EGval g p ν Dpm o w)) = (∑ ρ, ν ρ - Dpm + 2 * o) * Real.log g

def DegreeTermWithError : Prop :=
  ∀ (Pl : Type) [Fintype Pl] [DecidableEq Pl] (TT : Finset Pl) (m : ℕ) (P : HarishChandraParameters Pl),
    HarishChandraParamConditions TT P.k P.t m P.u P.v P.e P.bb P.a P.bt P.b0 P.xq P.S P.η P.C → ∀ j : ℕ, 1 ≤ j → j ≤ m →
      |(∑ ρ, (P.deg j ρ : ℝ)) - P.Dpm m j - ((∑ ρ ∈ TT, (P.a ρ : ℝ)) + ∑ ρ ∈ univ \ TT, (P.e ρ j : ℝ))|
        ≤ (Fintype.card Pl : ℝ) * (((P.C : ℝ) + 3) * (P.k * P.S + m * P.t * P.η) + (P.k * P.S + m * P.η))
          + (TT.card : ℝ) * (((P.C : ℝ) + 3) * (P.b0 / P.xq))

def SecondComplementClosedValuation : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K] (g : Fin 2 → ℕ),
    (∀ i, 0 < g i) → Nat.Coprime (g 0) (g 1) →
    ∀ (Pl : Type) [Fintype Pl] (TT : Finset Pl) (m : ℕ) (P : HarishChandraParameters Pl)
      (E : Fin m → HeightOneSpectrum (𝓞 K) → ℝ), (∀ j, (Function.support (E j)).Finite) →
    ∀ (p : Fin 2 → Pl → K) (Dx : Fin m → Pl → ℕ),
    (∀ i ρ, p i ρ * star (p i ρ) = (g i : K)) → (∀ j ρ, (Dx j ρ : ℚ) = P.deg (j.val + 1) ρ) →
    ∀ (o : Fin m → Fin 2 → ℝ) (Eels : Fin m → ℝ) (x eps f b C0 : ℝ),
    (∀ j i w, PlOver (g i) w → E j w = (vw w (g i : K) : ℝ) *
      EGval (g i) (p i) (fun ρ => (Dx j ρ : ℝ)) (P.Dpm m (j.val + 1)) (o j i) w) →
    (∀ j, (∑ᶠ (w : HeightOneSpectrum (𝓞 K)) (_ : ∀ i, ¬ PlOver (g i) w), Formalism.DivisionValues.lw w * |E j w|) ≤ Eels j) →
    ParameterSizeInequalities P TT m x eps f b C0 (Real.log ((g 0 : ℝ) * (g 1 : ℝ))) → ErrorSizeConditions P TT m x eps f b C0 o Eels →
      TypePrimeCostDeviationBound TT (fun ρ => (P.a ρ : ℝ)) (fun j => ∑ᶠ w : HeightOneSpectrum (𝓞 K), Formalism.DivisionValues.lw w * E j w)
        (Real.log ((g 0 : ℝ) * (g 1 : ℝ))) (m : ℝ) (f * m * b * x ^ eps) C0

def FamilyParameterConditions {H : Type} [AddCommGroup H] [Fintype H] [DecidableEq H] {I : Type} {m : ℕ} (F : Fam I m) (u : I) (G : Glob)
    (TT : Finset H) (a : H → ℝ) (g : Fin 2 → ℕ) (C0 : ℝ) : Prop :=
  ∃ (P : HarishChandraParameters (PhiSet (H := H))) (p : Fin 2 → PhiSet (H := H) → F.K) (Dx : Fin m → PhiSet (H := H) → ℕ)
    (o : Fin m → Fin 2 → ℝ) (Eels : Fin m → ℝ),
    (∀ t ∈ TT, a t = (P.a (topPhi H t) : ℝ)) ∧
    (∀ i ρ, p i ρ * star (p i ρ) = (g i : F.K)) ∧
    (∀ j ρ, (Dx j ρ : ℚ) = P.deg (j.val + 1) ρ) ∧
    (∀ i (w : slopeLatticeData.FinPl F.K), prBelow w = g i → w ∈ F.S) ∧
    (∀ j i (z : HeightOneSpectrum (𝓞 F.K)), PlOver (g i) z →
      F.Ej u j (plOf z) = EGval (g i) (p i) (fun ρ => (Dx j ρ : ℝ)) (P.Dpm m (j.val + 1)) (o j i) z) ∧
    (∀ j, ∑ w ∈ F.S.filter (fun w => prBelow w ≠ g 0 ∧ prBelow w ≠ g 1), lE w * |F.Ej u j w| ≤ Eels j) ∧
    ParameterSizeInequalities P (TT.map (topPhi H)) m G.x G.ε (2 * (Fintype.card H : ℝ)) (Real.exp (G.x ^ G.ε)) C0
      (Real.log ((g 0 : ℝ) * (g 1 : ℝ))) ∧
    ErrorSizeConditions P (TT.map (topPhi H)) m G.x G.ε (2 * (Fintype.card H : ℝ)) (Real.exp (G.x ^ G.ε)) C0 o Eels

def FamilyPlacesAbovePrimeSum : Prop :=
  ∀ (I : Type) (m : ℕ) (F : Fam I m) (u : I) (j : Fin m) (g : ℕ), g.Prime →
    ∀ (Pl : Type) [Fintype Pl] (p : Pl → F.K), (∀ ρ, p ρ * star (p ρ) = (g : F.K)) → ∀ (ν : Pl → ℝ) (Dpm o : ℝ),
    (∀ w : slopeLatticeData.FinPl F.K, prBelow w = g → w ∈ F.S) →
    (∀ z : HeightOneSpectrum (𝓞 F.K), PlOver g z → F.Ej u j (plOf z) = EGval g p ν Dpm o z) →
      2 * ∑ w ∈ F.S.filter (fun w => prBelow w = g), lE w * F.Ej u j w = (∑ ρ, ν ρ - Dpm + 2 * o) * Real.log g

def FamilySecondComplement : Prop :=
  ∀ (H : Type) [AddCommGroup H] [Fintype H] [DecidableEq H] (I : Type) (m : ℕ) (F : Fam I m) (u : I) (G : Glob)
    (TT : Finset H) (a : H → ℝ) (g : Fin 2 → ℕ) (C0 : ℝ), (∀ i, (g i).Prime) → g 0 ≠ g 1 →
    FamilyParameterConditions F u G TT a g C0 →
      TypePrimeCostDeviationBound (TT.map (topPhi H)) (aPhi a) (Fam6.EAll F u) (Real.log ((g 0 : ℝ) * (g 1 : ℝ))) (m : ℝ) (budgetAtPoint H G m) C0

def TypePrimeCostBound : Prop :=
  ∀ (H : Type) [AddCommGroup H] [Fintype H] [DecidableEq H] (W : H → Type) [∀ u0, Fintype (W u0)] (m : ℕ)
    (G : Glob) (C : Consts) (D : ArithData H) (ell : AddChar (E0 × H) ℂ → ℂ) (N : ℕ) (TT T2 : Finset H)
    (a : H → ℝ) (w : H → Fin m → E0 × H → ℝ) (Fm : ∀ u0, Fam (W u0) m) (C0 : ℝ) (g : Fin 2 → ℕ),
    (∀ i, (g i).Prime) → g 0 ≠ g 1 → G.lg = Real.log ((g 0 : ℝ) * (g 1 : ℝ)) →
    9 * C0 ^ 2 + 6 * C0 + 20 ≤ C.cE →
    (∀ u0 (u : W u0), FamilyParameterConditions (Fm u0) u G TT a g C0) →
      EComp5 (mkData G C.cHH D ell N TT T2 a w Fm) C

def oGAt {D : Formalism.BasicNotions.D7} (L : Formalism.BasicNotions.SizeData₂ D) (c : Formalism.BasicNotions.ErrC) (dG : ℝ) : ℝ :=
  oG dG c.g (D.R.f : ℝ) (Formalism.MainNotions.G.Nm D) (D.R.m : ℝ) L.etaSz

def ResidueCharacteristicPlace : Prop :=
  ∀ (D : Formalism.BasicNotions.D7) (L : Formalism.BasicNotions.SizeData₂ D) (X : Formalism.BasicNotions.ErrX D) (c : Formalism.BasicNotions.ErrC) (i : Fin 2)
    (u : D.what₂.Word) (j : ℕ) (w : D.what₂.places.Pl), D.what₂.places.resChar w = D.host.g i →
    PlOver (D.host.g i) (D.plEq w) ∧
    vw (D.plEq w) (D.host.g i : D.what₂.LL) = (D.what₂.places.ramIdx w : ℤ) ∧
    (∀ τ, Formalism.BasicNotions.tauPib X i τ * star (Formalism.BasicNotions.tauPib X i τ) = (D.host.g i : D.what₂.LL)) ∧
    Formalism.BasicNotions.vNN X i u j w
      = vNNg (D.host.g i) (Formalism.BasicNotions.tauPib X i) (Formalism.BasicNotions.nuAbs D u j) (D.plEq w) ∧
    Formalism.BasicNotions.EatG L X c i u j w
      = EGval (D.host.g i) (Formalism.BasicNotions.tauPib X i) (Formalism.BasicNotions.nuAbs D u j) (Formalism.BasicNotions.fockDeg D j : ℝ) (oGAt L c 0)
          (D.plEq w)

def ClosedLossEvaluation : Prop :=
  ∀ (D : Formalism.BasicNotions.D7) (L : Formalism.BasicNotions.SizeData₂ D) (X : Formalism.BasicNotions.ErrX D) (Kc : Formalism.MainNotions.G.Consts) (c : Formalism.BasicNotions.ErrC)
    (i : Fin 2) (u : D.what₂.Word) (j : ℕ) (w : D.what₂.places.Pl), D.what₂.places.resChar w = D.host.g i →
    D.host.g i ≠ (D.mem u).A.T →
    Formalism.BasicNotions.Eval L X Kc c u j w
      = EGval (D.host.g i) (Formalism.BasicNotions.tauPib X i) (Formalism.BasicNotions.nuAbs D u j) (Formalism.BasicNotions.fockDeg D j : ℝ)
          (oGAt L c (padicValNat (D.host.g i) (D.mem u).C.DGam : ℝ)) (D.plEq w)

def hcU₂ (D : Formalism.BasicNotions.D7) (u : D.what₂.Word) (τ : D.what₂.Tau) (l : ℕ) : ℚ :=
  if h : 1 ≤ l ∧ l ≤ D.R.k then (D.hcW u τ).u ⟨l - 1, by omega⟩ else 0

def hcE₂ (D : Formalism.BasicNotions.D7) (τ : D.what₂.Tau) (l : ℕ) : ℚ :=
  if h : 1 ≤ l ∧ l ≤ D.R.m then (D.hc τ).e ⟨l - 1, by omega⟩ else 0

def PartitionSizeHarishChandra : Prop :=
  ∀ (D : Formalism.BasicNotions.D7) (u : D.what₂.Word) (j : ℕ) (τ : D.what₂.Tau), 1 ≤ j → j ≤ D.R.m →
    Formalism.BasicNotions.nuAbs D u j τ = ((HCdeg D.R.k D.R.t (hcU₂ D u τ) (hcE₂ D τ) j : ℚ) : ℝ)

def ClosedLossSumIdentity : Prop :=
  ∀ (D : Formalism.BasicNotions.D7) (L : Formalism.BasicNotions.SizeData₂ D) (X : Formalism.BasicNotions.ErrX D) (Kc : Formalism.MainNotions.G.Consts) (c : Formalism.BasicNotions.ErrC)
    (i : Fin 2) (u : D.what₂.Word) (j : ℕ), D.host.g i ≠ (D.mem u).A.T →
    2 * (∑ᶠ (z : HeightOneSpectrum (𝓞 D.what₂.LL)) (_ : PlOver (D.host.g i) z),
      Formalism.DivisionValues.lw z * ((vw z (D.host.g i : D.what₂.LL) : ℝ) * Formalism.BasicNotions.Eval L X Kc c u j (D.plEq.symm z)))
      = (∑ τ, Formalism.BasicNotions.nuAbs D u j τ - (Formalism.BasicNotions.fockDeg D j : ℝ)
          + 2 * oGAt L c (padicValNat (D.host.g i) (D.mem u).C.DGam : ℝ)) * Real.log (D.host.g i)

def oGArith (N : Formalism.L2.DIV.NumDatum) (C : Formalism.L2.GlobalTheoryTheory.Arith.Cst) (Lv : Formalism.L2.GlobalTheoryTheory.Arith.Lev N) (i : Fin 2) : ℝ :=
  oG (padicValNat (N.g i) Lv.DGam : ℝ) C.err.g (N.R.f : ℝ) (N.Nm : ℝ) (N.R.m : ℝ) N.eta

def NormOfUniformiserConjugate : Prop :=
  ∀ (N : Formalism.L2.DIV.NumDatum) (C : Formalism.L2.GlobalTheoryTheory.Arith.Cst) (Lv : Formalism.L2.GlobalTheoryTheory.Arith.Lev N),
    Formalism.L2.GlobalTheoryTheory.Arith.Lev.admitted N Lv → N.g 0 ≠ N.g 1 →
    ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (sd : K), sd ^ 2 = -(N.d : K) → star sd = -sd →
    ∀ i : Fin 2,
      Formalism.L2.GlobalTheoryTheory.Arith.eltBar sd (Lv.piG i) * star (Formalism.L2.GlobalTheoryTheory.Arith.eltBar sd (Lv.piG i)) = (N.g i : K) ∧
      ∀ w : HeightOneSpectrum (𝓞 K),
        (Formalism.L2.GlobalTheoryTheory.Arith.pOf w = N.g i ↔ PlOver (N.g i) w) ∧
        (PlOver (N.g i) w → (Formalism.BasicNotions.eWL K w : ℝ) = (vw w (N.g i : K) : ℝ)) ∧
        ∀ (δ : Formalism.L2.DIV.Code N) (j : ℕ), PlOver (N.g i) w → N.g i ≠ Lv.T δ →
          Formalism.L2.GlobalTheoryTheory.Arith.E N C Lv sd δ j w
            = EGval (N.g i) (fun _ : Unit => Formalism.L2.GlobalTheoryTheory.Arith.eltBar sd (Lv.piG i))
                (fun _ => ((N.Dpi δ j : ℚ) : ℝ)) ((N.Dplus j + N.Dminus j : ℚ) : ℝ) (oGArith N C Lv i) w

def ClosedLossSizeSum : Prop :=
  ∀ (N : Formalism.L2.DIV.NumDatum) (C : Formalism.L2.GlobalTheoryTheory.Arith.Cst) (Lv : Formalism.L2.GlobalTheoryTheory.Arith.Lev N),
    Formalism.L2.GlobalTheoryTheory.Arith.Lev.admitted N Lv → N.g 0 ≠ N.g 1 →
    ∀ (K : Type) [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K] (sd : K), sd ^ 2 = -(N.d : K) →
    star sd = -sd → ∀ (i : Fin 2) (δ : Formalism.L2.DIV.Code N) (j : ℕ), N.g i ≠ Lv.T δ →
      ∑ᶠ (w : HeightOneSpectrum (𝓞 K)) (_ : Formalism.L2.GlobalTheoryTheory.Arith.pOf w = N.g i),
        Formalism.L2.GlobalTheoryTheory.Arith.sz w (Formalism.L2.GlobalTheoryTheory.Arith.E N C Lv sd δ j w)
        = (((N.Dpi δ j : ℚ) : ℝ) - ((N.Dplus j + N.Dminus j : ℚ) : ℝ) + 2 * oGArith N C Lv i) * Real.log (N.g i)

def arU (N : Formalism.L2.DIV.NumDatum) (δ : Formalism.L2.DIV.Code N) (z : Formalism.L2.DIV.RPl N.R) (l : ℕ) : ℚ :=
  if h : 1 ≤ l ∧ l ≤ N.R.k then N.uW δ z ⟨l - 1, by omega⟩ else 0

def arV (N : Formalism.L2.DIV.NumDatum) (z : Formalism.L2.DIV.RPl N.R) (l : ℕ) : ℚ :=
  if h : 2 ≤ l ∧ l ≤ N.R.k then (N.hc z).v ⟨l - 2, by omega⟩ else 0

def arB (N : Formalism.L2.DIV.NumDatum) (z : Formalism.L2.DIV.RPl N.R) (l : ℕ) : ℚ :=
  if h : 1 ≤ l ∧ l ≤ N.R.m then (N.hc z).b ⟨l - 1, by omega⟩ else 0

def arE (N : Formalism.L2.DIV.NumDatum) (z : Formalism.L2.DIV.RPl N.R) (l : ℕ) : ℚ := N.eQ l z

def DatumDegreesHarishChandra : Prop :=
  ∀ (N : Formalism.L2.DIV.NumDatum) (δ : Formalism.L2.DIV.Code N) (j : ℕ), 1 ≤ j → j ≤ N.R.m →
    (∀ z, N.nuAbs δ j z = HCdeg N.R.k N.R.t (arU N δ z) (arE N z) j) ∧
    N.Dpi δ j = ∑ z, HCdeg N.R.k N.R.t (arU N δ z) (arE N z) j ∧
    N.Dplus j = ∑ z, HCDplus N.R.k N.R.t N.R.m j (arV N z) (arB N z) (arE N z) ∧
    N.Dminus j = ∑ z, HCDminus N.R.k N.R.t N.R.m j (arV N z) (arB N z) (arE N z)

def TypePrimeLeadingTerm : Prop :=
  ∀ (N : Formalism.L2.DIV.NumDatum) (δ : Formalism.L2.DIV.Code N) (TT : Finset (Formalism.L2.DIV.RPl N.R))
    (a bt : Formalism.L2.DIV.RPl N.R → ℚ) (b0 xq S η C : ℚ),
    HarishChandraParamConditions TT N.R.k N.R.t N.R.m (arU N δ) (arV N) (arE N) (arB N) a bt b0 xq S η C →
    ∀ j : ℕ, 1 ≤ j → j ≤ N.R.m →
      |((N.Dpi δ j : ℚ) : ℝ) - ((N.Dplus j + N.Dminus j : ℚ) : ℝ)
          - ((∑ z ∈ TT, (a z : ℝ)) + ∑ z ∈ univ \ TT, N.w j z)|
        ≤ (Fintype.card (Formalism.L2.DIV.RPl N.R) : ℝ)
            * (((C : ℝ) + 3) * (N.R.k * S + N.R.m * N.R.t * η) + (N.R.k * S + N.R.m * η))
          + (TT.card : ℝ) * (((C : ℝ) + 3) * (b0 / xq))

def arPar (N : Formalism.L2.DIV.NumDatum) (δ : Formalism.L2.DIV.Code N) (a bt : Formalism.L2.DIV.RPl N.R → ℚ) (b0 xq S η C : ℚ)
    (Nn w'' X'' logd : ℝ) : HarishChandraParameters (Formalism.L2.DIV.RPl N.R) :=
  { k := N.R.k, t := N.R.t, u := arU N δ, v := arV N, e := arE N, bb := arB N, a := a, bt := bt, b0 := b0, xq := xq,
    S := S, η := η, C := C, N := Nn, w'' := w'', X'' := X'', logd := logd }

def ArithmeticSecondComplement : Prop :=
  ∀ (N : Formalism.L2.DIV.NumDatum) (C : Formalism.L2.GlobalTheoryTheory.Arith.Cst) (Lv : Formalism.L2.GlobalTheoryTheory.Arith.Lev N),
    Formalism.L2.GlobalTheoryTheory.Arith.Lev.admitted N Lv → N.g 0 ≠ N.g 1 →
    ∀ (K : Type) [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K] (sd : K), sd ^ 2 = -(N.d : K) →
    star sd = -sd → ∀ δ : Formalism.L2.DIV.Code N, (∀ i, N.g i ≠ Lv.T δ) →
    ∀ (TT : Finset (Formalism.L2.DIV.RPl N.R)) (a bt : Formalism.L2.DIV.RPl N.R → ℚ) (b0 xq S η Cc : ℚ) (Nn w'' X'' logd : ℝ)
      (Dx : Fin N.R.m → Formalism.L2.DIV.RPl N.R → ℕ), (∀ j z, (Dx j z : ℚ) = N.nuAbs δ (j.val + 1) z) →
    ∀ E : Fin N.R.m → HeightOneSpectrum (𝓞 K) → ℝ, (∀ j, (Function.support (E j)).Finite) →
    (∀ j i w, PlOver (N.g i) w →
      E j w = (Formalism.BasicNotions.eWL K w : ℝ) * Formalism.L2.GlobalTheoryTheory.Arith.E N C Lv sd δ (j.val + 1) w) →
    ∀ (Eels : Fin N.R.m → ℝ) (x eps f b C0 : ℝ),
    (∀ j, (∑ᶠ (w : HeightOneSpectrum (𝓞 K)) (_ : ∀ i, ¬ PlOver (N.g i) w), Formalism.DivisionValues.lw w * |E j w|) ≤ Eels j) →
    ParameterSizeInequalities (arPar N δ a bt b0 xq S η Cc Nn w'' X'' logd) TT N.R.m x eps f b C0
      (Real.log ((N.g 0 : ℝ) * (N.g 1 : ℝ))) →
    ErrorSizeConditions (arPar N δ a bt b0 xq S η Cc Nn w'' X'' logd) TT N.R.m x eps f b C0 (fun _ i => oGArith N C Lv i) Eels →
      TypePrimeCostDeviationBound TT (fun z => (a z : ℝ)) (fun j => ∑ᶠ w : HeightOneSpectrum (𝓞 K), Formalism.DivisionValues.lw w * E j w)
        (Real.log ((N.g 0 : ℝ) * (N.g 1 : ℝ))) (N.R.m : ℝ) (f * N.R.m * b * x ^ eps) C0

end Formalism.AtG
