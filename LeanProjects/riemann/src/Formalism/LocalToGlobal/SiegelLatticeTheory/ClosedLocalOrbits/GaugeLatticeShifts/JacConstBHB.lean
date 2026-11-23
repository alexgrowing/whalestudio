import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.JacConst

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal

namespace Formalism.L2.SG.Pf.BH

open Formalism.QuantumDeterminants Formalism.L2.SG.Pf

def rhs (k r : ℕ) (μb : Measure (Mt k r)) (φ : Mt k r → ℝ≥0∞) : ℝ≥0∞ :=
  ∫⁻ c : Fin r → ℂ, ENNReal.ofReal (Formalism.FourierDecayAlt.B2.cWeight k r c) *
    ∫⁻ n, ∫⁻ m, ∫⁻ n', φ (fun i j => (Matrix.of n * bigCell k r c 1 * Matrix.of m * (Matrix.of n')⁻¹) i j)
      ∂(Formalism.MainNotions.S.haarLie (Nset k r) 1) ∂μb ∂(Formalism.MainNotions.S.haarLie (Nset k r) 1)

def w0B (k r : ℕ) : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ := bigCell k r 1 1

def gBall (k r : ℕ) (ρ : ℝ) : Set (Mt k r) := expBall (k := k) (r := r) (UH (Hpk k r)) ρ

def wBall (k r : ℕ) (ρ : ℝ) : Set (Mt k r) :=
  {x | (fun i j => (w0B k r * Matrix.of x) i j) ∈ gBall k r ρ}

def gVol (k r : ℕ) (ρ : ℝ) : ℝ :=
  (volume (Metric.ball (0 : Formalism.MainNotions.S.lieE (UH (Hpk k r))) ρ)).toReal

def IterGauge : Prop :=
  ∀ (k r : ℕ) (μ μb : Measure (Mt k r)), IsGaugeOn (UH (Hpk k r)) μ → IsGaugeOn (Formalism.FourierDecayAlt.B2.UWb k r) μb →
    ∃ C : NNReal, 0 < C ∧ ∀ φ : Mt k r → ℝ≥0∞, Measurable φ → ∫⁻ x, φ x ∂μ = (C : ℝ≥0∞) * rhs k r μb φ

def GaugeShift : Prop :=
  ∀ (k r : ℕ) (μ : Measure (Mt k r)), Formalism.MainNotions.S.IsHaarOn (UH (Hpk k r)) μ → ∀ ρ : ℝ, 0 < ρ →
    MeasurableSet (wBall k r ρ) ∧ μ (wBall k r ρ) = μ (gBall k r ρ)

def RhsLim : Prop :=
  ∀ (k r : ℕ) (μb : Measure (Mt k r)), IsGaugeOn (Formalism.FourierDecayAlt.B2.UWb k r) μb →
    Tendsto (fun ρ : ℝ => (rhs k r μb ((wBall k r ρ).indicator 1)).toReal / gVol k r ρ) (𝓝[>] 0)
      (𝓝 ((2 : ℝ) ^ r)⁻¹)

end Formalism.L2.SG.Pf.BH
