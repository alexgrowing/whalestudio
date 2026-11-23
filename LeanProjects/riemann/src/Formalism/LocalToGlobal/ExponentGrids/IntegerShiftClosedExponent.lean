import Mathlib
import Formalism.LocalToGlobal.Divisibility.Inputs
import Formalism.LocalToGlobal.ExponentGrids.SecondComplementClosedValuation
import Formalism.TranslateCocycles.Statement
import Formalism.TranslateCocycles.StatementCEStep

open Module NumberField IsDedekindDomain Finset
open Formalism.DivisionValues (vw conjPl PlOver)
open Formalism.L2.Indef (DefBase DefSide DefCols SPer IndefNum IndefCore)
open Formalism.L2.GlobalTheoryTheory (Arith.Cst Arith.Lev Arith.Lev.admitted Arith.sg Arith.elt Arith.eltBar Arith.pOf Arith.EatT)

noncomputable section

namespace Formalism.AtG

section Defs

variable {K : Type} [Field K] [NumberField K]

def PerBd [StarRing K] {Bs : DefBase K} {Df : DefSide Bs} (Dc : DefCols Df) (u : Dc.Mem)
    (Nu : Submodule (𝓞 K) (Fin (Dc.a u) → K)) (t : Bs.Tup) (w : HeightOneSpectrum (𝓞 K)) (s : ℝ) : Prop :=
  ∀ φ ∈ Nu, ∀ F ∈ Df.Mt t, Dc.Pt u t φ F = 0 ∨ s ≤ (vw w (Dc.Pt u t φ F) : ℝ)

def colRhs {J : Type} (s : Finset J) (g : ℕ) (nn : J → K) (cg : K) (E0 : ℝ) (w : HeightOneSpectrum (𝓞 K)) : ℝ :=
  -(∑ j ∈ s, (vw w (nn j) : ℝ)) + (vw w cg : ℝ) - E0 * (vw w (g : K) : ℝ)

def liftExponentAtPlace (g : ℕ) (Fj : ℝ) (nn : K) (CE f N m η : ℝ) (w : HeightOneSpectrum (𝓞 K)) : ℝ :=
  Fj + (vw w nn : ℝ) / (vw w (g : K) : ℝ) + CE * f * (N ^ 2 + m ^ 2 * η)

variable (K) in

def sgOf {J : Type} (s : Finset J) (g : ℕ) (gain F E : J → ℝ) (w : HeightOneSpectrum (𝓞 K)) : ℝ :=
  (vw w (g : K) : ℝ) * ∑ j ∈ s, (gain j + F j - E j)

end Defs

def chainMap {K : Type} [Field K] (V : ℕ → Type) [∀ i, AddCommGroup (V i)] [∀ i, Module K (V i)]
    (Kj : ∀ i, V i →ₗ[K] V (i + 1)) : ∀ n, V 0 →ₗ[K] V n
  | 0 => LinearMap.id
  | n + 1 => (Kj n).comp (chainMap V Kj n)

def PeriodBoundAllPlaces : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (Bs : DefBase K) (Df0 Df1 : DefSide Bs) (Dc : DefCols Df1)
    (Sp : SPer Dc) (Nn : IndefNum Bs) (P : IndefCore Df0 Df1 Dc Sp Nn) (u : Dc.Mem)
    (Nu : Submodule (𝓞 K) (Fin (Dc.a u) → K)) (sg : HeightOneSpectrum (𝓞 K) → ℝ),
    ((∀ w, PerBd Dc u Nu (P.cols.μ w) w (sg w)) ↔
      ∀ w, ∀ φ ∈ Nu, ∀ F ∈ Df1.Mt (P.cols.μ w),
        Dc.Pt u (P.cols.μ w) φ F = 0 ∨ sg w ≤ (vw w (Dc.Pt u (P.cols.μ w) φ F) : ℝ)) ∧
    ∀ (Pl : Type) [Fintype Pl] [DecidableEq Pl] (R : Formalism.L2.DIV.RecNums Bs.J Pl),
      Formalism.L2.DIV.DivInputs P R u Nu sg → ∀ w, PerBd Dc u Nu (P.cols.μ w) w (sg w)

def RootOfUnityIsUnit : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (c : K) (n : ℕ), 0 < n → c ^ n = 1 →
    ∀ w : HeightOneSpectrum (𝓞 K), vw w c = 0

def ShiftValueZeroGain : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (g : ℕ) (w : HeightOneSpectrum (𝓞 K)), PlOver g w →
    ∀ (J : Type) (s : Finset J) (nn : J → K) (CE f m N η : ℝ) (F : J → ℝ), (s.card : ℝ) = m →
      sgOf K s g (fun _ => 0) F (fun j => liftExponentAtPlace g (F j) (nn j) CE f N m η w) w
        = -(∑ j ∈ s, (vw w (nn j) : ℝ)) - m * CE * f * (N ^ 2 + m ^ 2 * η) * (vw w (g : K) : ℝ)

def ValuationBoundAtGlobalPlace : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (Bs : DefBase K) (Df : DefSide Bs) (Dc : DefCols Df)
    (u : Dc.Mem) (Nu : Submodule (𝓞 K) (Fin (Dc.a u) → K)) (t : Bs.Tup) (g : ℕ)
    (w : HeightOneSpectrum (𝓞 K)), PlOver g w →
    ∀ (J : Type) (s : Finset J) (nn : J → K) (cg : K) (C CE f m N tt η : ℝ) (gain F E : J → ℝ),
    (s.card : ℝ) = m → 0 ≤ C → 0 ≤ f → 0 ≤ N → 0 ≤ tt → tt ≤ N → 0 ≤ η → 2 * C ≤ CE →
    (∃ n : ℕ, 0 < n ∧ cg ^ n = 1) → (∀ j ∈ s, gain j = 0) →
    (∀ j ∈ s, liftExponentAtPlace g (F j) (nn j) CE f N m η w ≤ E j) →
    PerBd Dc u Nu t w (colRhs s g nn cg (C * f * m * N * (N + tt)) w) →
      PerBd Dc u Nu t w (sgOf K s g gain F E w)

def LatticeMapChain : Prop :=
  ∀ (K : Type) [Field K] (V : ℕ → Type) [∀ i, AddCommGroup (V i)] [∀ i, Module K (V i)]
    (Kj : ∀ i, V i →ₗ[K] V (i + 1)) (L : ∀ i, Set (V i)) (a : ℕ → K) (n : ℕ),
    (∀ i, i < n → ∀ x ∈ L i, ∃ y ∈ L (i + 1), Kj i x = a i • y) →
    ∀ x ∈ L 0, ∃ y ∈ L n, chainMap V Kj n x = (∏ i ∈ range n, a i) • y

def ColumnChainBound : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (Bs : DefBase K) (Df : DefSide Bs) (Dc : DefCols Df)
    (u : Dc.Mem) (Nu : Submodule (𝓞 K) (Fin (Dc.a u) → K)) (t : Bs.Tup) (w : HeightOneSpectrum (𝓞 K))
    (V : ℕ → Type) [∀ i, AddCommGroup (V i)] [∀ i, Module K (V i)] (Kj : ∀ i, V i →ₗ[K] V (i + 1))
    (L : ∀ i, Set (V i)) (a : ℕ → K) (n : ℕ) (Pr : V n →ₗ[K] Module.Dual K (Fin (Df.nV t) → K)),
    (∀ i, i < n → a i ≠ 0) →
    (∀ i, i < n → ∀ x ∈ L i, ∃ y ∈ L (i + 1), Kj i x = a i • y) →
    (∀ y ∈ L n, ∀ F ∈ Df.Mt t, Pr y F = 0 ∨ 0 ≤ vw w (Pr y F)) →
    (∀ φ ∈ Nu, ∃ x ∈ L 0, Dc.Pt u t φ = Pr (chainMap V Kj n x)) →
      PerBd Dc u Nu t w (∑ i ∈ range n, (vw w (a i) : ℝ)) ∧
      ∀ (J : Type) (s : Finset J) (g : ℕ) (nn : J → K) (cg : K) (E0 : ℝ),
        colRhs s g nn cg E0 w ≤ ∑ i ∈ range n, (vw w (a i) : ℝ) → PerBd Dc u Nu t w (colRhs s g nn cg E0 w)

def ScalarsValuationSum : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (g : ℕ), 0 < g → ∀ (w : HeightOneSpectrum (𝓞 K)) (n : ℕ)
    (sh nn : ℕ → K) (e : ℕ → ℤ), (∀ i, i < n → sh i ≠ 0) → (∀ i, i < n → nn i ≠ 0) →
      (∀ i, i < n → sh i * (nn i)⁻¹ * (g : K) ^ (e i) ≠ 0) ∧
      ∑ i ∈ range n, (vw w (sh i * (nn i)⁻¹ * (g : K) ^ (e i)) : ℝ)
        = -(∑ i ∈ range n, (vw w (nn i) : ℝ)) + (vw w (∏ i ∈ range n, sh i) : ℝ)
          + ((∑ i ∈ range n, e i : ℤ) : ℝ) * (vw w (g : K) : ℝ)

def ValuationBoundAtGlobalPlaceChain : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (Bs : DefBase K) (Df : DefSide Bs) (Dc : DefCols Df)
    (u : Dc.Mem) (Nu : Submodule (𝓞 K) (Fin (Dc.a u) → K)) (t : Bs.Tup) (g : ℕ)
    (w : HeightOneSpectrum (𝓞 K)), PlOver g w →
    ∀ (V : ℕ → Type) [∀ i, AddCommGroup (V i)] [∀ i, Module K (V i)] (Kj : ∀ i, V i →ₗ[K] V (i + 1))
    (L : ∀ i, Set (V i)) (a : ℕ → K) (n : ℕ) (Pr : V n →ₗ[K] Module.Dual K (Fin (Df.nV t) → K)),
    (∀ i, i < n → a i ≠ 0) →
    (∀ i, i < n → ∀ x ∈ L i, ∃ y ∈ L (i + 1), Kj i x = a i • y) →
    (∀ y ∈ L n, ∀ F ∈ Df.Mt t, Pr y F = 0 ∨ 0 ≤ vw w (Pr y F)) →
    (∀ φ ∈ Nu, ∃ x ∈ L 0, Dc.Pt u t φ = Pr (chainMap V Kj n x)) →
    ∀ (J : Type) (s : Finset J) (nn : J → K) (cg : K) (C CE f m N tt η : ℝ) (gain F E : J → ℝ),
    colRhs s g nn cg (C * f * m * N * (N + tt)) w ≤ ∑ i ∈ range n, (vw w (a i) : ℝ) →
    (s.card : ℝ) = m → 0 ≤ C → 0 ≤ f → 0 ≤ N → 0 ≤ tt → tt ≤ N → 0 ≤ η → 2 * C ≤ CE →
    (∃ k : ℕ, 0 < k ∧ cg ^ k = 1) → (∀ j ∈ s, gain j = 0) →
    (∀ j ∈ s, liftExponentAtPlace g (F j) (nn j) CE f N m η w ≤ E j) →
      PerBd Dc u Nu t w (sgOf K s g gain F E w)

def ValuationBoundAtGlobalPlaceDerivation : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (Bs : DefBase K) (Df : DefSide Bs) (Dc : DefCols Df)
    (u : Dc.Mem) (Nu : Submodule (𝓞 K) (Fin (Dc.a u) → K)) (t : Bs.Tup) (g : ℕ)
    (w : HeightOneSpectrum (𝓞 K)), PlOver g w →
    ∀ (V : ℕ → Type) [∀ i, AddCommGroup (V i)] [∀ i, Module K (V i)] (Kj : ∀ i, V i →ₗ[K] V (i + 1))
    (L : ∀ i, Set (V i)) (sh nn : ℕ → K) (e : ℕ → ℤ) (n : ℕ)
    (Pr : V n →ₗ[K] Module.Dual K (Fin (Df.nV t) → K)),
    (∀ i, i < n → nn i ≠ 0) →
    (∀ i, i < n → ∀ x ∈ L i, ∃ y ∈ L (i + 1), Kj i x = (sh i * (nn i)⁻¹ * (g : K) ^ (e i)) • y) →
    (∀ y ∈ L n, ∀ F ∈ Df.Mt t, Pr y F = 0 ∨ 0 ≤ vw w (Pr y F)) →
    (∀ φ ∈ Nu, ∃ x ∈ L 0, Dc.Pt u t φ = Pr (chainMap V Kj n x)) →
    (∃ k : ℕ, 0 < k ∧ (∏ i ∈ range n, sh i) ^ k = 1) →
    ∀ (C CE f N tt η : ℝ) (gain F E : ℕ → ℝ),
    -(C * f * (n : ℝ) * N * (N + tt)) ≤ ((∑ i ∈ range n, e i : ℤ) : ℝ) →
    0 ≤ C → 0 ≤ f → 0 ≤ N → 0 ≤ tt → tt ≤ N → 0 ≤ η → 2 * C ≤ CE →
    (∀ j ∈ range n, gain j = 0) →
    (∀ j ∈ range n, liftExponentAtPlace g (F j) (nn j) CE f N (n : ℝ) η w ≤ E j) →
      PerBd Dc u Nu t w (sgOf K (range n) g gain F E w)

def BaseTuplePeriodChain : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (Bs : DefBase K) (Df : DefSide Bs) (Dc : DefCols Df)
    (u : Dc.Mem) (ch : Formalism.L2.DIV.ColChain Dc u) (Nu : Submodule (𝓞 K) (Fin (Dc.a u) → K))
    (w : HeightOneSpectrum (𝓞 K)) (L : ∀ i, Set (Fin (ch.c i) → K)) (a : Fin ch.mm → K),
    (∀ j, a j ≠ 0) →
    (∀ j : Fin ch.mm, ∀ x ∈ L j.castSucc, ∃ y ∈ L j.succ, (ch.Kj j).mulVec x = a j • y) →
    (∀ y ∈ L (Fin.last ch.mm), ∀ F ∈ Df.Mt Bs.μ0, ch.PtL y F = 0 ∨ 0 ≤ vw w (ch.PtL y F)) →
    (∀ φ ∈ Nu, (fun i => φ (Fin.cast ch.c0 i)) ∈ L 0) →
      PerBd Dc u Nu Bs.μ0 w (∑ j, (vw w (a j) : ℝ))

def NonzeroContentTwisted : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (Bs : DefBase K) (Df0 Df1 : DefSide Bs) (Dc : DefCols Df1)
    (Sp : SPer Dc) (Nn : IndefNum Bs) (P : IndefCore Df0 Df1 Dc Sp Nn) (w : HeightOneSpectrum (𝓞 K)) (j : Bs.J),
    Nn.F0 w j ≠ 0 → P.cols.μ w ≠ Bs.μ0

def ScalarsAgainstColumnBound : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (g : ℕ) (w : HeightOneSpectrum (𝓞 K)), PlOver g w →
    ∀ (m : ℕ) (sh nn : ℕ → K) (e : ℕ → ℤ) (E0 : ℝ), (∀ i, i < m → sh i ≠ 0) → (∀ i, i < m → nn (i + 1) ≠ 0) →
    -E0 ≤ ((∑ i ∈ range m, e i : ℤ) : ℝ) →
      colRhs (Finset.Icc 1 m) g nn (∏ i ∈ range m, sh i) E0 w
        ≤ ∑ i ∈ range m, (vw w (sh i * (nn (i + 1))⁻¹ * (g : K) ^ (e i)) : ℝ)

def ConjugatePairBalance : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (Bs : DefBase K) (Df : DefSide Bs) (Dc : DefCols Df)
    (u : Dc.Mem) (Nu : Submodule (𝓞 K) (Fin (Dc.a u) → K)) (t : Bs.Tup) (g : ℕ)
    (w : HeightOneSpectrum (𝓞 K)), PlOver g w →
    ∀ (T : Type) [Fintype T] (a : T → K), (∀ τ, a τ * star (a τ) = (g : K)) →
    ∀ (s : Finset ℕ) (D : ℕ → T → ℕ) (CE f m N η : ℝ) (F F' : ℕ → ℝ), (s.card : ℝ) = m →
    PerBd Dc u Nu t w
      (sgOf K s g (fun _ => 0) F (fun j => liftExponentAtPlace g (F j) (∏ τ, a τ ^ D j τ) CE f N m η w) w) →
    PerBd Dc u Nu t (conjPl w)
      (sgOf K s g (fun _ => 0) F' (fun j => liftExponentAtPlace g (F' j) (∏ τ, a τ ^ D j τ) CE f N m η (conjPl w)) (conjPl w)) →
    ∀ φ ∈ Nu, ∀ X ∈ Df.Mt t, Dc.Pt u t φ X ≠ 0 →
      -(∑ j ∈ s, ((∑ τ, D j τ : ℕ) : ℝ)) - 2 * (m * CE * f * (N ^ 2 + m ^ 2 * η))
        ≤ (vw w (Dc.Pt u t φ X) : ℝ) / (vw w (g : K) : ℝ)
          + (vw (conjPl w) (Dc.Pt u t φ X) : ℝ) / (vw w (g : K) : ℝ)

def IntegerShiftClosedExponent : Prop :=
  ∀ (N : Formalism.L2.DIV.NumDatum) (C : Arith.Cst) (Lv : Arith.Lev N) (K : Type) [Field K] [NumberField K] (sd : K)
    (δ : Formalism.L2.DIV.Code N),
    Formalism.L2.DIV.shiftZ (fun w : HeightOneSpectrum (𝓞 K) => (Formalism.BasicNotions.eWL K w : ℝ) * Arith.sg N C Lv sd δ w)
      = Formalism.L2.GlobalTheoryTheory.Arith.sgExp N C Lv sd δ

def NormPrimeNoInertGain : Prop :=
  ∀ (N : Formalism.L2.DIV.NumDatum) (C : Arith.Cst) (Lv : Arith.Lev N) (p : ℕ) (A B : ℤ), p.Prime →
    A ^ 2 + (N.d : ℤ) * B ^ 2 = 4 * (p : ℤ) →
    ¬ (N.cls p = Formalism.BasicNotions.PrimeClass.inertClass ∨ N.cls p = Formalism.BasicNotions.PrimeClass.signal) ∧
    ∀ j, Formalism.L2.GlobalTheoryTheory.Arith.gainD N C Lv p j = 0

def TypePrimeNotLevelPrime : Prop :=
  ∀ (N : Formalism.L2.DIV.NumDatum) (Lv : Arith.Lev N), Arith.Lev.admitted N Lv → ∀ δ ∈ Lv.Ws, ∀ i, N.g i ≠ Lv.T δ

def ClosedShiftArithmetic : Prop :=
  ∀ (N : Formalism.L2.DIV.NumDatum) (C : Arith.Cst) (Lv : Arith.Lev N), Arith.Lev.admitted N Lv →
    ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (sd : K), sd ^ 2 = -(N.d : K) → star sd = -sd →
    ∀ (i : Fin 2) (δ : Formalism.L2.DIV.Code N), N.g i ≠ Lv.T δ →
    oGArith N C Lv i = C.err.g * (N.R.f : ℝ) * ((N.Nm : ℝ) ^ 2 + (N.R.m : ℝ) ^ 2 * N.eta) ∧
    ∀ w : HeightOneSpectrum (𝓞 K), PlOver (N.g i) w →
      (Formalism.BasicNotions.eWL K w : ℝ) * Arith.sg N C Lv sd δ w
        = -(∑ j ∈ N.lifts, ((N.Dpi δ j : ℚ) : ℝ) * (vw w (Arith.eltBar sd (Lv.piG i)) : ℝ))
          - (N.R.m : ℝ) * C.err.g * (N.R.f : ℝ) * ((N.Nm : ℝ) ^ 2 + (N.R.m : ℝ) ^ 2 * N.eta) * (vw w (N.g i : K) : ℝ)

def ValuationBoundAtGlobalPlaceArithmetic : Prop :=
  ∀ (N : Formalism.L2.DIV.NumDatum) (C : Arith.Cst) (Lv : Arith.Lev N), Arith.Lev.admitted N Lv →
    ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (sd : K), sd ^ 2 = -(N.d : K) → star sd = -sd →
    ∀ (i : Fin 2) (δ : Formalism.L2.DIV.Code N), N.g i ≠ Lv.T δ →
    ∀ (Dx : ℕ → ℕ), (∀ j ∈ N.lifts, ((Dx j : ℕ) : ℚ) = N.Dpi δ j) →
    ∀ (cg : K) (Cc : ℝ), (∃ n : ℕ, 0 < n ∧ cg ^ n = 1) → 0 ≤ Cc → 2 * Cc ≤ C.err.g →
    ∀ (Bs : DefBase K) (Df : DefSide Bs) (Dc : DefCols Df) (u : Dc.Mem)
      (Nu : Submodule (𝓞 K) (Fin (Dc.a u) → K)) (t : Bs.Tup) (w : HeightOneSpectrum (𝓞 K)), PlOver (N.g i) w →
    PerBd Dc u Nu t w (colRhs N.lifts (N.g i) (fun j => Arith.eltBar sd (Lv.piG i) ^ Dx j) cg
      (Cc * (N.R.f : ℝ) * (N.R.m : ℝ) * (N.Nm : ℝ) * ((N.Nm : ℝ) + (N.R.t : ℝ))) w) →
      PerBd Dc u Nu t w ((Formalism.BasicNotions.eWL K w : ℝ) * Arith.sg N C Lv sd δ w)

def ValuationBoundArithmetic : Prop :=
  ∀ (N : Formalism.L2.DIV.NumDatum) (C : Arith.Cst) (Lv : Arith.Lev N), Arith.Lev.admitted N Lv →
    ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (sd : K), sd ^ 2 = -(N.d : K) → star sd = -sd →
    ∀ (δ : Formalism.L2.DIV.Code N), (∀ i, N.g i ≠ Lv.T δ) →
    ∀ (Dx : ℕ → ℕ), (∀ j ∈ N.lifts, ((Dx j : ℕ) : ℚ) = N.Dpi δ j) →
    ∀ (cg : Fin 2 → K) (Cc : ℝ), (∀ i, ∃ n : ℕ, 0 < n ∧ cg i ^ n = 1) → 0 ≤ Cc → 2 * Cc ≤ C.err.g →
    ∀ (Bs : DefBase K) (Df0 Df1 : DefSide Bs) (Dc : DefCols Df1) (Sp : SPer Dc) (Nn : IndefNum Bs)
      (P : IndefCore Df0 Df1 Dc Sp Nn) (u : Dc.Mem) (Nu : Submodule (𝓞 K) (Fin (Dc.a u) → K)),
    (∀ i w, PlOver (N.g i) w →
      PerBd Dc u Nu (P.cols.μ w) w (colRhs N.lifts (N.g i) (fun j => Arith.eltBar sd (Lv.piG i) ^ Dx j) (cg i)
        (Cc * (N.R.f : ℝ) * (N.R.m : ℝ) * (N.Nm : ℝ) * ((N.Nm : ℝ) + (N.R.t : ℝ))) w)) →
    (∀ w, (∀ i, ¬ PlOver (N.g i) w) →
      PerBd Dc u Nu (P.cols.μ w) w ((Formalism.BasicNotions.eWL K w : ℝ) * Arith.sg N C Lv sd δ w)) →
      ∀ w, ∀ φ ∈ Nu, ∀ F ∈ Df1.Mt (P.cols.μ w),
        Dc.Pt u (P.cols.μ w) φ F = 0 ∨
          (Formalism.BasicNotions.eWL K w : ℝ) * Arith.sg N C Lv sd δ w ≤ (vw w (Dc.Pt u (P.cols.μ w) φ F) : ℝ)

def ValuationBoundHypotheses : Prop :=
  ∀ (N : Formalism.L2.DIV.NumDatum) (C : Arith.Cst) (Lv : Arith.Lev N), Arith.Lev.admitted N Lv →
    ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (sd : K), sd ^ 2 = -(N.d : K) → star sd = -sd →
    ∀ (δ : Formalism.L2.DIV.Code N), (∀ i, N.g i ≠ Lv.T δ) →
    ∀ (Dx : ℕ → ℕ), (∀ j ∈ N.lifts, ((Dx j : ℕ) : ℚ) = N.Dpi δ j) →
    ∀ (cg : Fin 2 → K) (Cc : ℝ), (∀ i, ∃ n : ℕ, 0 < n ∧ cg i ^ n = 1) → 0 ≤ Cc → 2 * Cc ≤ C.err.g →
    ∀ (Bs : DefBase K) (Df0 Df1 : DefSide Bs) (Dc : DefCols Df1) (Sp : SPer Dc) (Nn : IndefNum Bs)
      (P : IndefCore Df0 Df1 Dc Sp Nn) (u : Dc.Mem) (Nu : Submodule (𝓞 K) (Fin (Dc.a u) → K))
      (Pl : Type) [Fintype Pl] [DecidableEq Pl] (R : Formalism.L2.DIV.RecNums Bs.J Pl),
    ∀ I0 : Formalism.L2.DIV.DivInputs0 P R u Nu (fun w => (Formalism.BasicNotions.eWL K w : ℝ) * Arith.sg N C Lv sd δ w),
    (∀ i w, PlOver (N.g i) w →
      PerBd Dc u Nu (P.cols.μ w) w (colRhs N.lifts (N.g i) (fun j => Arith.eltBar sd (Lv.piG i) ^ Dx j) (cg i)
        (Cc * (N.R.f : ℝ) * (N.R.m : ℝ) * (N.Nm : ℝ) * ((N.Nm : ℝ) + (N.R.t : ℝ))) w)) →
    (∀ w, (∀ i, ¬ PlOver (N.g i) w) →
      PerBd Dc u Nu (P.cols.μ w) w ((Formalism.BasicNotions.eWL K w : ℝ) * Arith.sg N C Lv sd δ w)) →
      ∃ I : Formalism.L2.DIV.DivInputs P R u Nu (fun w => (Formalism.BasicNotions.eWL K w : ℝ) * Arith.sg N C Lv sd δ w),
        I.toDivInputs0 = I0

def ClosedShiftLevelPrime : Prop :=
  ∀ (N : Formalism.L2.DIV.NumDatum) (C : Arith.Cst) (Lv : Arith.Lev N), Arith.Lev.admitted N Lv →
    ∀ (K : Type) [Field K] [NumberField K] (sd : K) (δ : Formalism.L2.DIV.Code N), δ ∈ Lv.Ws →
    ∀ w : HeightOneSpectrum (𝓞 K), Arith.pOf w = Lv.T δ →
      (0 < Formalism.BasicNotions.vAdd w (Arith.elt sd (Lv.piT δ)) → Arith.sg N C Lv sd δ w = -((N.R.m : ℝ) * Arith.EatT N δ)) ∧
      (¬ 0 < Formalism.BasicNotions.vAdd w (Arith.elt sd (Lv.piT δ)) → Arith.sg N C Lv sd δ w = 0)

def ValuationBoundAtTupleArithmetic : Prop :=
  ∀ (N : Formalism.L2.DIV.NumDatum) (C : Arith.Cst) (Lv : Arith.Lev N), Arith.Lev.admitted N Lv →
    ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (sd : K) (δ : Formalism.L2.DIV.Code N), δ ∈ Lv.Ws →
    ∀ (Bs : DefBase K) (Df : DefSide Bs) (Dc : DefCols Df) (u : Dc.Mem)
      (Nu : Submodule (𝓞 K) (Fin (Dc.a u) → K)) (t : Bs.Tup) (w : HeightOneSpectrum (𝓞 K)), Arith.pOf w = Lv.T δ →
    (0 < Formalism.BasicNotions.vAdd w (Arith.elt sd (Lv.piT δ)) →
      PerBd Dc u Nu t w (-((Formalism.BasicNotions.eWL K w : ℝ) * ((N.R.m : ℝ) * Arith.EatT N δ)))) →
    (¬ 0 < Formalism.BasicNotions.vAdd w (Arith.elt sd (Lv.piT δ)) → PerBd Dc u Nu t w 0) →
      PerBd Dc u Nu t w ((Formalism.BasicNotions.eWL K w : ℝ) * Arith.sg N C Lv sd δ w)

end Formalism.AtG
