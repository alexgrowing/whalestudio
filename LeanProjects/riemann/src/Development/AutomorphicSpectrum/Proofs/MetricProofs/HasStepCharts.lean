import Mathlib
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Pull1
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsPeriodOn

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.StepW

open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Φ : Type} [Field Φ]
  {y : (Σ k, ι k) → Φ} {Ψ : Type} {N j n : ℕ}
  {Kk : Type} [Fintype Kk] {ιk : Kk → Type} [∀ k, Fintype (ιk k)]

def grMat (C : Matrix (Fin N) (Fin N) ℂ) (B : Finset (Fin N) → Matrix (Fin N) (Fin N) ℂ)
    (I₀ : Finset (Fin N)) (w : Finset (Fin N) → ℂ) : Matrix (Fin N) (Fin N) ℂ :=
  C + ∑ I, (w I / w I₀) • B I

def IsGrChart (N j : ℕ) (i : Fin N) (I₀ : Finset (Fin N)) (C : Matrix (Fin N) (Fin N) ℂ)
    (B : Finset (Fin N) → Matrix (Fin N) (Fin N) ℂ) : Prop :=
  ∀ (h : Matrix (Fin N) (Fin N) ℂ) (a : ℂ) (w : Finset (Fin N) → ℂ), IsBlockDiag j h → h.det ≠ 0 → a ≠ 0 →
    (∀ I, IsStepRows N j i I → w I = a * minorIJ h I (stepCols N j i)) → w I₀ ≠ 0 →
      IsBlockDiag j (grMat C B I₀ w) ∧ (grMat C B I₀ w).det ≠ 0 ∧
        ∀ I, minorIJ (grMat C B I₀ w) I (stepCols N j i) * w I₀ = a * minorIJ h I (stepCols N j i)

def plk (M : FlagModel y Ψ N j) (F : FrameData ι Ψ N M.Ω M.blk) (k₀ : K) (z : (Σ k, ι k) → ℂ)
    (I : Finset (Fin N)) : ℂ :=
  ∑ m : ι k₀, valAt M.x (F.u' I ⟨k₀, m⟩) (basePart M.blk z) * z ⟨k₀, m⟩

def baseMono (M : FlagModel y Ψ N j) (F : FrameData ι Ψ N M.Ω M.blk) (p : Ψ × Fin N) (z : (Σ k, ι k) → ℂ) : ℂ :=
  ∏ k : NonPluckerBlocks M.blk, basePart M.blk z ⟨k, F.c k⟩ ^ M.dy p k.1

def stepGap (M : FlagModel y Ψ N j) (BM : BaseMetric M n) (p : Ψ × Fin N) (z : (Σ k, ι k) → ℂ) : ℝ :=
  Real.log ((BM.hom p).h z) - Real.log ((fsHerm ι (M.dy p)).h z)

def stepPh (M : FlagModel y Ψ N j) (BM : BaseMetric M n) (p : Ψ × Fin N)
    (v : (Σ k, ιk k) → (Σ k, ι k)) {e : ℕ} (R : AnLogRes (mCoordIdeal (y ∘ v)) ⊤ e)
    (pr : R.X → BM.Rb.X) (x : R.X) : ℝ :=
  if h : pr x ∉ bdry BM.s ∧ ∃ z ∈ mcPts (mCoordIdeal y), z ∘ v = R.lift x x then stepGap M BM p h.2.choose else 0

def IsStepHyp (M : FlagModel y Ψ N j) (BM : BaseMetric M n) (p : Ψ × Fin N) (κ : Kk → K)
    (v : (Σ k, ιk k) → (Σ k, ι k)) {e : ℕ} (R : AnLogRes (mCoordIdeal (y ∘ v)) ⊤ e)
    (pr : R.X → BM.Rb.X) : Prop :=
  IsBlockMap κ v ∧ (∀ k, ((∀ p', M.blk p' ≠ some k) ∨ M.blk p = some k) → k ∈ Set.range κ) ∧
    HoloMap R.A BM.Rb.A pr ∧
    ∀ x, ∃ z ∈ mcPts (mCoordIdeal y), z ∘ v = R.lift x x ∧
      SameOrbit (basePart M.blk z) (BM.Rb.lift (pr x) (pr x))

def IsStepChart (M : FlagModel y Ψ N j) (BM : BaseMetric M n) (p : Ψ × Fin N) (κ : Kk → K)
    (v : (Σ k, ιk k) → (Σ k, ι k)) {e : ℕ} (R : AnLogRes (mCoordIdeal (y ∘ v)) ⊤ e)
    (pr : R.X → BM.Rb.X) (x y₀ : R.X) (W : Set R.X) (l : Fin BM.q)
    (H : R.X → Matrix (Fin N) (Fin N) ℂ) (D : R.X → ℂ) : Prop :=
  IsOpen W ∧ y₀ ∈ W ∧ W ⊆ R.U x ∧ (∀ y' ∈ W, pr y' ∈ BM.O l) ∧
    (∀ a b, R.A.HoloOn W fun y' => H y' a b) ∧ (∀ y' ∈ W, IsBlockDiag j (H y') ∧ (H y').det ≠ 0) ∧
    R.A.HoloOn W D ∧ (∀ y' ∈ W, D y' ≠ 0) ∧
    ∀ y' ∈ W, pr y' ∉ bdry BM.s →
      Real.log ((fsHerm ιk fun k => M.dy p (κ k)).h (R.lift x y')) + stepPh M BM p v R pr y' =
        blockPot j p.2 (BM.G l p.1 (pr y')) (H y') + Real.log ‖D y'‖

def HasStepCharts (M : FlagModel y Ψ N j) (BM : BaseMetric M n) (p : Ψ × Fin N) (κ : Kk → K)
    (v : (Σ k, ιk k) → (Σ k, ι k)) {e : ℕ} (R : AnLogRes (mCoordIdeal (y ∘ v)) ⊤ e)
    (pr : R.X → BM.Rb.X) : Prop :=
  ∀ x y₀, y₀ ∈ R.U x → ∃ W l H D, IsStepChart M BM p κ v R pr x y₀ W l H D

end GlobalTheory.CompanionTheory.Ar.PB.StepW
