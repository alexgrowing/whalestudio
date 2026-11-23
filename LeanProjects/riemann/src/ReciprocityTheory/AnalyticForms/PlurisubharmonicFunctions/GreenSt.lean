import Mathlib
import ReciprocityTheory.AnalyticForms.MaIntEmpty

namespace ReciprocityTheory.AnForm.A

open MeasureTheory
open scoped Laplacian

noncomputable section

def ddcDens (u : ℂ → ℝ) (z : ℂ) : ℝ :=
  (1 / (2 * Real.pi)) * Δ u z

def ddcCoordDens {n : ℕ} (j : Fin n) (u : (Fin n → ℂ) → ℝ) (z : Fin n → ℂ) : ℝ :=
  (2 / Real.pi) * ReciprocityTheory.AnForm.levi u z (Pi.single j 1)

def LeviOneEqLaplacianStatement : Prop :=
  ∀ (u : ℂ → ℝ) (z : ℂ),
    ReciprocityTheory.AnForm.levi (fun w : Fin 1 → ℂ => u (w 0)) (fun _ => z) (Pi.single 0 1) =
      Δ u z / 4

def GreenOriginStatement : Prop :=
  ∀ u : ℂ → ℝ, ContDiff ℝ 2 u → HasCompactSupport u →
    Integrable (fun z : ℂ => Real.log ‖z‖ * Δ u z) ∧
      ∫ z : ℂ, Real.log ‖z‖ * Δ u z = 2 * Real.pi * u 0

def GreenDdcOriginStatement : Prop :=
  ∀ u : ℂ → ℝ, ContDiff ℝ 2 u → HasCompactSupport u →
    Integrable (fun z : ℂ => Real.log ‖z‖ * ddcDens u z) ∧
      ∫ z : ℂ, Real.log ‖z‖ * ddcDens u z = u 0

def GreenPointStatement : Prop :=
  ∀ (u : ℂ → ℝ) (a : ℂ), ContDiff ℝ 2 u → HasCompactSupport u →
    Integrable (fun z : ℂ => Real.log ‖z - a‖ * Δ u z) ∧
      ∫ z : ℂ, Real.log ‖z - a‖ * Δ u z = 2 * Real.pi * u a

def GreenParamFiberStatement : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (u : ℂ × E → ℝ), ContDiff ℝ 2 u → HasCompactSupport u → ∀ p : E,
    Integrable (fun z : ℂ => Real.log ‖z‖ * Δ (fun w : ℂ => u (w, p)) z) ∧
      ∫ z : ℂ, Real.log ‖z‖ * Δ (fun w : ℂ => u (w, p)) z = 2 * Real.pi * u (0, p)

def GreenParamStatement : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [IsFiniteMeasureOnCompacts μ]
    (u : ℂ × E → ℝ), ContDiff ℝ 2 u → HasCompactSupport u →
    Integrable (fun q : ℂ × E => Real.log ‖q.1‖ * Δ (fun w : ℂ => u (w, q.2)) q.1)
        ((volume : Measure ℂ).prod μ) ∧
      ∫ q : ℂ × E, Real.log ‖q.1‖ * Δ (fun w : ℂ => u (w, q.2)) q.1 ∂((volume : Measure ℂ).prod μ)
        = 2 * Real.pi * ∫ p : E, u (0, p) ∂μ

def GreenCoordStatement : Prop :=
  ∀ (D : ℕ) (j : Fin (D + 1)) (u : (Fin (D + 1) → ℂ) → ℝ), ContDiff ℝ 2 u → HasCompactSupport u →
    Integrable (fun z : Fin (D + 1) → ℂ => Real.log ‖z j‖ * ddcCoordDens j u z) ∧
      ∫ z : Fin (D + 1) → ℂ, Real.log ‖z j‖ * ddcCoordDens j u z =
        ∫ w : Fin D → ℂ, u (Fin.insertNth j 0 w)

def GreenCoordFiberStatement : Prop :=
  ∀ (D : ℕ) (j : Fin (D + 1)) (u : (Fin (D + 1) → ℂ) → ℝ), ContDiff ℝ 2 u → HasCompactSupport u →
    ∀ w : Fin D → ℂ,
    Integrable (fun ζ : ℂ => Real.log ‖ζ‖ * ddcCoordDens j u (Fin.insertNth j ζ w)) ∧
      ∫ ζ : ℂ, Real.log ‖ζ‖ * ddcCoordDens j u (Fin.insertNth j ζ w) = u (Fin.insertNth j 0 w)

def GreenCoordZeroStatement : Prop :=
  ∀ (D : ℕ) (u : (Fin (D + 1) → ℂ) → ℝ), ContDiff ℝ 2 u → HasCompactSupport u →
    Integrable (fun z : Fin (D + 1) → ℂ => Real.log ‖z 0‖ * ddcCoordDens 0 u z) ∧
      ∫ z : Fin (D + 1) → ℂ, Real.log ‖z 0‖ * ddcCoordDens 0 u z =
        ∫ w : Fin D → ℂ, u (Fin.cons 0 w)

def GreenMaDensStatement : Prop :=
  ∀ u : (Fin 1 → ℂ) → ℝ, ContDiff ℝ 2 u → HasCompactSupport u →
    Integrable (fun z : Fin 1 → ℂ => Real.log ‖z 0‖ * ReciprocityTheory.AnForm.maDens ![u] z) ∧
      ∫ z : Fin 1 → ℂ, Real.log ‖z 0‖ * ReciprocityTheory.AnForm.maDens ![u] z = u 0

def GreenMixedStatement : Prop :=
  ∀ (D : ℕ) (j a b : Fin (D + 1)) (u : (Fin (D + 1) → ℂ) → ℝ), ContDiff ℝ 2 u → HasCompactSupport u →
    (a, b) ≠ (j, j) →
    Integrable (fun z : Fin (D + 1) → ℂ => (Real.log ‖z j‖ : ℂ) * ReciprocityTheory.AnForm.hessC u z a b) ∧
      ∫ z : Fin (D + 1) → ℂ, (Real.log ‖z j‖ : ℂ) * ReciprocityTheory.AnForm.hessC u z a b = 0

theorem hyp_inhabited_bump : ∃ u : ℂ → ℝ, ContDiff ℝ 2 u ∧ HasCompactSupport u ∧ u 0 = 1 := by
  let b : ContDiffBump (0 : ℂ) := ⟨1, 2, one_pos, one_lt_two⟩
  exact ⟨b, b.contDiff, b.hasCompactSupport, b.one_of_mem_closedBall (by simpa using b.rIn_pos.le)⟩

end

end ReciprocityTheory.AnForm.A
