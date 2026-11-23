import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.PlaceDegreeData
import Development.AbelianVarietyTheory.BlockTheory.SiegelWeilLocal.DefiniteGapThreshold
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsWeakIntegralOfStronglyContinuous
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CuspidalSubspaceClosedRightTranslationStable

open MeasureTheory NumberField Matrix
open scoped InnerProductSpace
open Formalism.MainNotions.S Formalism.MainNotions.PlaceDegreeData GlobalTheory.IndefiniteRowSideFullHecke.IsotropicFlagConstantTerms

noncomputable section

namespace GlobalTheory.GlobalProjectorCompare

section Test

variable (I : AutInst) {H : InfinitePlace I.F → Type} [∀ v, NormedAddCommGroup (H v)]
  [∀ v, InnerProductSpace ℂ (H v)] (σ : ∀ v, Matrix (Fin I.n) (Fin I.n) ℂ → (H v →L[ℂ] H v)) (w : ∀ v, H v)

end Test

def AutomorphicCountingData (n₀ : ℕ) (A : ℝ) (I : AutInst) (lam : InfinitePlace I.F → Fin I.n → ℝ) (μf : Measure I.Gf)
    (e : I.Gf → ℂ) : Prop :=
  ∃ (b : ℝ) (g g₀ : ℕ), HidaSetting I n₀ A b lam μf g g₀ e

def LowGapIntegrable (n₀ : ℕ) (A : ℝ) : Prop :=
  ∀ (I : AutInst) (b : ℝ) (lam : InfinitePlace I.F → Fin I.n → ℝ) (g g₀ : ℕ) (e : I.Gf → ℂ)
    (H : InfinitePlace I.F → Type) [∀ v, NormedAddCommGroup (H v)] [∀ v, InnerProductSpace ℂ (H v)]
    [∀ v, CompleteSpace (H v)] (σ : ∀ v, Matrix (Fin I.n) (Fin I.n) ℂ → (H v →L[ℂ] H v)) (w : ∀ v, H v)
    (Hs : Type) [NormedAddCommGroup Hs] [InnerProductSpace ℂ Hs] [CompleteSpace Hs]
    (σs : I.Ginf → (Hs →L[ℂ] Hs)) (tens : (∀ v, H v) → Hs) (μf : Measure I.Gf) [SigmaFinite μf]
    (fund : Set I.GA) (R : I.GA → (I.L2 μf fund →L[ℂ] I.L2 μf fund))
    (Re : I.L2 μf fund →L[ℂ] I.L2 μf fund) (h : ℝ),
    HidaSetting I n₀ A b lam μf g g₀ e → CountData I lam σ w σs tens μf fund R e Re →
    (∀ v, Formalism.QuantumDeterminants.GapAtLeast (I.ε v) (lam v) h) →
    (∀ v, 120 * (I.n : ℝ) * (q0At I v : ℝ) ^ ((3 : ℝ) / 2) ≤ h) →
    Integrable (phOf I σ w) (Measure.pi fun v => Formalism.REAL.muG (I.ε v))

def FiniteHom (n₀ : ℕ) (A C : ℝ) : Prop :=
  ∀ (I : AutInst) (b : ℝ) (lam : InfinitePlace I.F → Fin I.n → ℝ) (g g₀ : ℕ) (e : I.Gf → ℂ)
    (H : InfinitePlace I.F → Type) [∀ v, NormedAddCommGroup (H v)] [∀ v, InnerProductSpace ℂ (H v)]
    [∀ v, CompleteSpace (H v)] (σ : ∀ v, Matrix (Fin I.n) (Fin I.n) ℂ → (H v →L[ℂ] H v)) (w : ∀ v, H v)
    (Hs : Type) [NormedAddCommGroup Hs] [InnerProductSpace ℂ Hs] [CompleteSpace Hs]
    (σs : I.Ginf → (Hs →L[ℂ] Hs)) (tens : (∀ v, H v) → Hs) (μf : Measure I.Gf) [SigmaFinite μf]
    (fund : Set I.GA) (R : I.GA → (I.L2 μf fund →L[ℂ] I.L2 μf fund))
    (Re : I.L2 μf fund →L[ℂ] I.L2 μf fund) (h : ℝ),
    HidaSetting I n₀ A b lam μf g g₀ e → CountData I lam σ w σs tens μf fund R e Re →
    (∀ v, Formalism.QuantumDeterminants.GapAtLeast (I.ε v) (lam v) h) →
    (∀ v, 120 * (I.n : ℝ) * (q0At I v : ℝ) ^ ((3 : ℝ) / 2) ≤ h) →
    (∀ v, C * (I.n : ℝ) ^ 2 * Real.sqrt (q0At I v : ℝ) ≤ h) →
    FiniteDimensional ℂ (I.eHom σs μf fund R Re)

def PointwiseCusp (n₀ : ℕ) (A C : ℝ) : Prop :=
  ∀ (I : AutInst) (b : ℝ) (lam : InfinitePlace I.F → Fin I.n → ℝ) (g g₀ : ℕ) (e : I.Gf → ℂ)
    (H : InfinitePlace I.F → Type) [∀ v, NormedAddCommGroup (H v)] [∀ v, InnerProductSpace ℂ (H v)]
    [∀ v, CompleteSpace (H v)] (σ : ∀ v, Matrix (Fin I.n) (Fin I.n) ℂ → (H v →L[ℂ] H v)) (w : ∀ v, H v)
    (Hs : Type) [NormedAddCommGroup Hs] [InnerProductSpace ℂ Hs] [CompleteSpace Hs]
    (σs : I.Ginf → (Hs →L[ℂ] Hs)) (tens : (∀ v, H v) → Hs) (μf : Measure I.Gf) [SigmaFinite μf]
    (fund : Set I.GA) (R : I.GA → (I.L2 μf fund →L[ℂ] I.L2 μf fund))
    (Re : I.L2 μf fund →L[ℂ] I.L2 μf fund) (h : ℝ),
    HidaSetting I n₀ A b lam μf g g₀ e → CountData I lam σ w σs tens μf fund R e Re →
    (∀ v, Formalism.QuantumDeterminants.GapAtLeast (I.ε v) (lam v) h) →
    (∀ v, 120 * (I.n : ℝ) * (q0At I v : ℝ) ^ ((3 : ℝ) / 2) ≤ h) →
    (∀ v, C * (I.n : ℝ) ^ 2 * Real.sqrt (q0At I v : ℝ) ≤ h) →
    ∀ T : I.L2 μf fund →L[ℂ] I.L2 μf fund, I.IsRConv μf fund R (phe I (phOf I σ w) e) T →
      ∀ Fv ∈ LinearMap.range (T : I.L2 μf fund →ₗ[ℂ] I.L2 μf fund), IsCuspClass I μf fund Fv

variable (I : AutInst)

def oneStep (W : Submodule I.E (Fin I.n → I.E)) : ℕ → Submodule I.E (Fin I.n → I.E) :=
  fun i => if i = 0 then ⊥ else W

end GlobalTheory.GlobalProjectorCompare
