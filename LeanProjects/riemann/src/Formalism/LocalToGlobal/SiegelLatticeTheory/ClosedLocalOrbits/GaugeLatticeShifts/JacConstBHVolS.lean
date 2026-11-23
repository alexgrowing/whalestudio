import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.JacConstBHR

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal Matrix

namespace Formalism.L2.SG.Pf.BH

open Formalism.QuantumDeterminants Formalism.L2.SG.Pf

def DimG : Prop :=
  ∀ k r : ℕ, Module.finrank ℝ (Formalism.MainNotions.S.lieE (UH (Hpk k r))) =
    2 * Module.finrank ℝ (Formalism.MainNotions.S.lieE (Nset k r)) + 2 * r + Module.finrank ℝ (Formalism.MainNotions.S.lieE (Formalism.FourierDecayAlt.B2.UWb k r))

def LieG : Prop :=
  ∀ k r : ℕ, Formalism.MainNotions.S.lieOf (UH (Hpk k r)) = {X | Hpk k r * Xᴴ * Hpk k r + X = 0}

def LieWb : Prop :=
  ∀ k r : ℕ, Formalism.MainNotions.S.lieOf (Formalism.FourierDecayAlt.B2.UWb k r) = {X | Hpk k r * Xᴴ * Hpk k r + X = 0 ∧
    ∀ a : Fin r, X *ᵥ bvec (eI k r a) = 0 ∧ X *ᵥ bvec (esI k r a) = 0}

def DimGOf : Prop := LieG → LieWb → DimG

def expL (k r : ℕ) (S : Set (Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)) (Y : Formalism.MainNotions.S.lieE S) : Mt k r :=
  fun i j => NormedSpace.exp (Formalism.MainNotions.S.unrealify (Y : EuclideanSpace ℝ _)) i j

def RhoN : Prop :=
  ∀ (k r : ℕ) (Y : Formalism.MainNotions.S.lieE (Nset k r)), rhoS k r (Nset k r) (expL k r (Nset k r) Y) = (‖Y‖₊ : ℝ≥0∞)

def RhoMeas : Prop :=
  ∀ (k r : ℕ) (S : Set (Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)), Measurable (rhoS k r S)

def LayerCmp : Prop :=
  ∀ (X Y : Type) [MeasurableSpace X] [MeasurableSpace Y] (μ : Measure X) (ν : Measure Y) (q : X → ℝ≥0∞)
    (p : Y → ℝ≥0∞), Measurable q → Measurable p → ∀ δ c : ℝ≥0∞,
    (∀ t, t < δ → μ {x | q x < t} ≤ c * ν {y | p y < t}) → (∀ t, t < δ → ν {y | p y < t} ≠ ∞) →
    ∀ g : ℝ≥0∞ → ℝ≥0∞, Antitone g → (∀ x, g x ≠ ∞) → (∀ x, δ ≤ x → g x = 0) →
      ∫⁻ x, g (q x) ∂μ ≤ c * ∫⁻ y, g (p y) ∂ν

def ModelVol : Prop :=
  ∀ (E1 E2 : Type) [NormedAddCommGroup E1] [InnerProductSpace ℝ E1] [FiniteDimensional ℝ E1] [MeasurableSpace E1]
    [BorelSpace E1] [NormedAddCommGroup E2] [InnerProductSpace ℝ E2] [FiniteDimensional ℝ E2] [MeasurableSpace E2]
    [BorelSpace E2] (r : ℕ) (s : ℝ), 0 < s →
    ∫⁻ c : Fin r → ℂ, ∫⁻ y1 : E1, ∫⁻ y2 : E2, ∫⁻ y3 : E1,
      (if (‖y1‖₊ : ℝ≥0∞) ^ 2 + ENNReal.ofReal (2 * ∑ a, ‖c a - 1‖ ^ 2) + (‖y2‖₊ : ℝ≥0∞) ^ 2 + (‖y3‖₊ : ℝ≥0∞) ^ 2 <
          ENNReal.ofReal (s ^ 2) then (1 : ℝ≥0∞) else 0) =
      ENNReal.ofReal ((2 : ℝ) ^ r)⁻¹ *
        volume (Metric.ball (0 : EuclideanSpace ℝ (Fin (2 * Module.finrank ℝ E1 + 2 * r + Module.finrank ℝ E2))) s)

def BallDim : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E]
    [BorelSpace E] (s : ℝ),
    volume (Metric.ball (0 : E) s) = volume (Metric.ball (0 : EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) s)

end Formalism.L2.SG.Pf.BH
