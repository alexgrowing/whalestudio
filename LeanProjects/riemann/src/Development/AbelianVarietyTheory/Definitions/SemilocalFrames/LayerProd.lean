import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.GlobAut
import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
import Formalism.HarderNarasimhan.QuotRealize

open MeasureTheory NumberField Matrix Finset
open scoped InnerProductSpace

noncomputable section

namespace GlobalTheory.Count

open Formalism.MainNotions.S

def dOp {n : ℕ} (g : Matrix (Fin n) (Fin n) ℂ) : ℝ :=
  Real.log ‖LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin g)‖

def dHS {n : ℕ} (g : Matrix (Fin n) (Fin n) ℂ) : ℝ :=
  Real.sqrt (∑ j, (Real.log ((Matrix.isHermitian_conjTranspose_mul_self g).eigenvalues j) / 2) ^ 2)

def rkR {n : ℕ} (ε : Fin n → Bool) : ℕ :=
  min (univ.filter fun a => ε a = true).card (univ.filter fun a => ε a = false).card

def decE (q : ℕ) (h d : ℝ) : ℝ := Real.exp (-(h / 8) * min (2 * d ^ 2) (d / Real.sqrt q))

def IsGauge {n : ℕ} (ε : Fin n → Bool) (c : ℝ) : Prop :=
  Filter.Tendsto
    (fun r : ℝ => c * (Formalism.REAL.muG ε {g | Real.sqrt (Formalism.REAL.hs (uMat g - 1)) ≤ r}).toReal / r ^ (n ^ 2))
    (nhdsWithin 0 (Set.Ioi 0))
    (nhds (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin (n ^ 2))) 1)).toReal)

def layerProd (n f : ℕ) {a : ℕ} (j : Fin a → ℕ) (τ : Fin a → ℝ) (G : ℝ → ℝ) : ℝ :=
  (∏ i, ∏ k ∈ univ.filter (fun k => i < k),
      G (τ i / τ k) ^ (2 * j i * j k * f) * G (τ i * τ k) ^ (2 * j i * j k * f)) *
    ∏ i, G (τ i) ^ (2 * j i * (n - 2 * ∑ l, j l) * f) * G (τ i ^ 2) ^ (j i ^ 2 * f)

variable (I : AutInst)

def lamX (x : I.GA) : Submodule (𝓞 I.E) (Fin I.n → I.E) :=
  Submodule.span (𝓞 I.E)
    {y | I.fmat x.2⁻¹ *ᵥ (fun i => Formalism.UG.inclE (F := I.F) (Af I.F) (y i)) ∈ I.Lf}

open Classical in

def frm (x : I.GA) : InfinitePlace I.E → Matrix (Fin I.n) (Fin I.n) ℂ := fun w =>
  if w.embedding = I.φ (w.comap (algebraMap I.F I.E)) then
    I.P (w.comap (algebraMap I.F I.E)) * uMat (x.1 (w.comap (algebraMap I.F I.E)))
  else (I.P (w.comap (algebraMap I.F I.E)) * uMat (x.1 (w.comap (algebraMap I.F I.E)))).map (starRingEnd ℂ)

abbrev bas : Module.Basis (Fin I.n) I.E (Fin I.n → I.E) := Pi.basisFun I.E (Fin I.n)

def least (x : I.GA) : ℝ := Formalism.HN.leastSize (bas I) (frm I x) (lamX I x)

def tau1 (x : I.GA) : ℝ := min (1 / 2) (least I x)

def stepLe (x : I.GA) (t : ℝ) : Submodule (𝓞 I.E) (Fin I.n → I.E) :=
  sSup {N | N ≤ lamX I x ∧ N ≠ ⊥ ∧ Formalism.HN.largestSize (bas I) (frm I x) N ≤ t}

def stepLt (x : I.GA) (t : ℝ) : Submodule (𝓞 I.E) (Fin I.n → I.E) :=
  sSup {N | N ≤ lamX I x ∧ N ≠ ⊥ ∧ Formalism.HN.largestSize (bas I) (frm I x) N < t}

def HasFlag (x : I.GA) {a : ℕ} (S : Fin (a + 1) → Submodule (𝓞 I.E) (Fin I.n → I.E)) (τ : Fin a → ℝ) : Prop :=
  S 0 = ⊥ ∧ StrictMono S ∧ S (Fin.last a) = stepLt I x (1 / 2) ∧ StrictMono τ ∧
    (∀ i, 0 < τ i ∧ τ i < 1 / 2 ∧ S i.succ = stepLe I x (τ i) ∧
      Formalism.HN.sizeQ (bas I) (frm I x) (S i.succ) (S i.castSucc) = τ i) ∧
    ∀ t : ℝ, t < 1 / 2 → stepLe I x t ∈ Set.range S

def HasType (x : I.GA) {a : ℕ} (j : Fin a → ℕ) (τ : Fin a → ℝ) : Prop :=
  ∃ S, HasFlag I x S τ ∧ ∀ i, Formalism.HN.rkK (S i.succ) = Formalism.HN.rkK (S i.castSucc) + j i

def perpIn (x : I.GA) (S : Submodule (𝓞 I.E) (Fin I.n → I.E)) : Submodule (𝓞 I.E) (Fin I.n → I.E) :=
  Submodule.span (𝓞 I.E) {y | y ∈ lamX I x ∧ ∀ s ∈ S, Formalism.UG.hform (starRingEnd I.E) I.J s y = 0}

def nearSet (x : I.GA) (δ : ℝ) : Set I.GA :=
  {γ | γ ∈ I.GFset ∧ (x⁻¹ * γ * x).2 ∈ I.Kset ∧
    ∀ v, Real.sqrt (Formalism.REAL.hs (uMat ((x⁻¹ * γ * x).1 v) - 1)) ≤ δ}

def kern (φ : I.GA → ℂ) (x y : I.GA) : ℂ := ∑' γ : I.GFset, φ (x⁻¹ * γ.1 * y)

variable (B : RowsAut)

def IsDSData (d : InfinitePlace B.I.F → ℝ) : Prop :=
  ∀ v, Formalism.QuantumDeterminants.IsHCParam (B.lam v) ∧ IsDS (B.I.ε v) (B.lam v) (B.σ v) ∧
    IsLowUnit (B.I.ε v) (B.lam v) (B.σ v) (B.w v) ∧ IsFdeg (Formalism.REAL.muG (B.I.ε v)) (B.σ v) (d v)

def SigIs (p q : ℕ) : Prop := ∀ v, B.I.pAt v = p ∧ B.I.qAt v = q

def GapGe (h : ℝ) : Prop := ∀ v, Formalism.QuantumDeterminants.GapAtLeast (B.I.ε v) (B.lam v) h

def ph (d : InfinitePlace B.I.F → ℝ) (g : B.I.Ginf) : ℂ :=
  ((∏ v, d v : ℝ) : ℂ) * star (∏ v, ⟪B.w v, B.σ v (uMat (g v)) (B.w v)⟫_ℂ)

def phe (d : InfinitePlace B.I.F → ℝ) (x : B.I.GA) : ℂ := ph B d x.1 * B.e x.2

def mainTerm (d : InfinitePlace B.I.F → ℝ) : ℝ := B.I.Dstar (∏ v, d v) B.μf B.fund B.e

def prob (A : Set B.I.GA) : ℝ := ((B.I.muA B.μf) (A ∩ B.fund)).toReal / B.I.vol B.μf B.fund

def IsNear (d : InfinitePlace B.I.F → ℝ) (ep : ℝ) (x γ : B.I.GA) : Prop :=
  γ ∈ B.I.GFset ∧ phe B d (x⁻¹ * γ * x) ≠ 0 ∧ ∀ v, dHS (uMat ((x⁻¹ * γ * x).1 v)) ≤ ep

def bigX (b : ℝ) : ℝ := (B.I.n : ℝ) * B.I.f * B.I.rd * B.g * b

def epN : ℝ := 1 / 10 ^ 6 / ((B.I.n : ℝ) ^ 8 * (B.I.f : ℝ) ^ 2)

def tauStar (q : ℕ) (b : ℝ) : ℝ := (bigX B b)⁻¹ ^ (11 * q)

def CountHyp (Cg : ℝ) (n₀ : ℕ) (d : InfinitePlace B.I.F → ℝ) (p q : ℕ) (b : ℝ) : Prop :=
  IsDSData B d ∧ SigIs B p q ∧ n₀ ≤ B.I.n ∧ q ^ 2 ≤ B.I.n ∧
    Real.log B.I.rd ≤ Real.exp B.I.n ∧ Real.log B.I.f ≤ Real.sqrt B.I.n ∧ 2 ≤ b ∧
    Real.log b ≤ Real.exp (1 / 16 * B.I.n * B.I.f * Real.log B.I.n) ∧
    (∀ v a, |B.lam v a| ≤ b ^ 2) ∧ 1 ≤ B.g ∧ (B.g : ℝ) ≤ b ^ Cg ∧
    B.g₀.Prime ∧ 4 * B.I.n < B.g₀ ∧
    (Ideal.primesOver (Ideal.span {(B.g₀ : ℤ)}) (𝓞 B.I.E)).ncard = Module.finrank ℚ B.I.E ∧
    GapGe B (8 * 10 ^ 14 * (Cg + 4) * (B.I.n : ℝ) ^ 19 * (B.I.f : ℝ) ^ 5 * Real.log (b * B.I.rd))

end GlobalTheory.Count
