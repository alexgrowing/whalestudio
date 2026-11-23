import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.EquivariantL2Space
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.StDefs

noncomputable section

open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal

namespace ReciprocityTheory.ChartRestriction.DS.Mult1.S0

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B

def dimN (k r : ℕ) : ℕ := r * (2 * r + 2 * k + 1)

def bS (k r : ℕ) : ℝ := ((2 * r + k : ℕ) : ℝ) * (dimN k r : ℝ)

def q0 (k r : ℕ) : ℕ := min (k + r) (r + 1)

def bG (k r : ℕ) : ℝ := 2 * ReciprocityTheory.ChartRestriction.DS.Mult1.nR k r * (q0 k r : ℝ)

def muSL {k r : ℕ} (μW μN : Measure (Mt k r)) : Measure (Mt k r) :=
  (μW.prod μN).map fun p => ((Matrix.of p.1 * Matrix.of p.2 : Lap.Mat k r) : Mt k r)

def SIntFin : Prop :=
  ∀ (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (μW μN : Measure (Mt k r)),
    inWb k r z → 0 < Tz k r z →
    Formalism.MainNotions.S.IsHaarOn (UWset k r z) μW → Formalism.MainNotions.S.IsHaarOn (Nset k r) μN →
    ∀ b : ℝ, bS k r < b →
      (∫⁻ p : Mt k r × Mt k r, ENNReal.ofReal (gN (Matrix.of p.1 * Matrix.of p.2) ^ (-b)) ∂(μW.prod μN)) < ∞ ∧
      (∫⁻ p : Mt k r × Mt k r, ENNReal.ofReal (gN (Matrix.of p.2 * Matrix.of p.1) ^ (-b)) ∂(μW.prod μN)) < ∞

def HaarOnBridge : Prop :=
  ∀ (k r : ℕ) (U : Set (Mat k r)) (μ : Measure (Mt k r)),
    Formalism.FourierDecayAlt.B.IsHaarOn U μ → Formalism.MainNotions.S.IsHaarOn U μ

variable {k r : ℕ}

def BesselOrbitHypotheses {Vp : Type*} [NormedAddCommGroup Vp] [InnerProductSpace ℂ Vp] [CompleteSpace Vp]
    (z : Fin (2 * r + k + 1) → ℂ) (c : Fin r → ℂ) (u : Fin k → ℝ) (π : Lap.Mat k r → (Vp →L[ℂ] Vp))
    (μW μN μG : Measure (Mt k r)) (f : Lap.Mat k r → ℂ) (a : ℝ) : Prop :=
  Lap.IsBData z c u π μW μN ∧ Formalism.MainNotions.S.IsHaarOn (UH (Hpk k r)) μG ∧
    ContinuousOn f (UH (Hpk k r)) ∧ (∃ C : ℝ, ∀ g ∈ UH (Hpk k r), ‖f g‖ ≤ C * gN g ^ (-a)) ∧
    4 * max (bG k r) (bS k r) < a

def OrbitIntegralAbsConvergent : Prop :=
  ∀ (k r : ℕ) (Vp : Type) [NormedAddCommGroup Vp] [InnerProductSpace ℂ Vp] [CompleteSpace Vp]
    (z : Fin (2 * r + k + 1) → ℂ) (c : Fin r → ℂ) (u : Fin k → ℝ) (π : Lap.Mat k r → (Vp →L[ℂ] Vp))
    (μW μN μG : Measure (Mt k r)) (f : Lap.Mat k r → ℂ) (a : ℝ),
    BesselOrbitHypotheses z c u π μW μN μG f a → ∀ (ξ : Vp), ∀ x ∈ UH (Hpk k r),
      Integrable (fun p : Mt k r × Mt k r => f (Matrix.of p.1 * Matrix.of p.2 * x) •
        Lap.chiInv (Formalism.MainNotions.S.psiGen k r z c) π (Matrix.of p.1) (Matrix.of p.2) ξ) (μW.prod μN)

def OrbitIntegralContinuous : Prop :=
  ∀ (k r : ℕ) (Vp : Type) [NormedAddCommGroup Vp] [InnerProductSpace ℂ Vp] [CompleteSpace Vp]
    (z : Fin (2 * r + k + 1) → ℂ) (c : Fin r → ℂ) (u : Fin k → ℝ) (π : Lap.Mat k r → (Vp →L[ℂ] Vp))
    (μW μN μG : Measure (Mt k r)) (f : Lap.Mat k r → ℂ) (a : ℝ),
    BesselOrbitHypotheses z c u π μW μN μG f a → ∀ ξ : Vp,
      ContinuousOn (Lap.sInt μW μN (Formalism.MainNotions.S.psiGen k r z c) π f ξ) (UH (Hpk k r))

def OrbitIntegralEquivariant : Prop :=
  ∀ (k r : ℕ) (Vp : Type) [NormedAddCommGroup Vp] [InnerProductSpace ℂ Vp] [CompleteSpace Vp]
    (z : Fin (2 * r + k + 1) → ℂ) (c : Fin r → ℂ) (u : Fin k → ℝ) (π : Lap.Mat k r → (Vp →L[ℂ] Vp))
    (μW μN μG : Measure (Mt k r)) (f : Lap.Mat k r → ℂ) (a : ℝ),
    BesselOrbitHypotheses z c u π μW μN μG f a → ∀ ξ : Vp,
      Formalism.MainNotions.S.IsSPsiEquiv z (Formalism.MainNotions.S.psiGen k r z c) π (Lap.sInt μW μN (Formalism.MainNotions.S.psiGen k r z c) π f ξ)

def OrbitIntegralMemL2 : Prop :=
  ∀ (k r : ℕ) (Vp : Type) [NormedAddCommGroup Vp] [InnerProductSpace ℂ Vp] [CompleteSpace Vp]
    (z : Fin (2 * r + k + 1) → ℂ) (c : Fin r → ℂ) (u : Fin k → ℝ) (π : Lap.Mat k r → (Vp →L[ℂ] Vp))
    (μW μN μG : Measure (Mt k r)) (f : Lap.Mat k r → ℂ) (a : ℝ),
    BesselOrbitHypotheses z c u π μW μN μG f a → ∀ (ξ : Vp) (ν : Measure (Mt k r)),
      Formalism.MainNotions.S.IsQuotMeas μG (muSL μW μN) ν →
      Lap.sInt μW μN (Formalism.MainNotions.S.psiGen k r z c) π f ξ ∈ Lap.equivariantL2Space z (Formalism.MainNotions.S.psiGen k r z c) π μG ν

def OrbitIntegralProperties : Prop := OrbitIntegralAbsConvergent ∧ OrbitIntegralContinuous ∧ OrbitIntegralEquivariant ∧ OrbitIntegralMemL2

def SOrbBound : Prop :=
  ∀ (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (μW μN : Measure (Mt k r)),
    inWb k r z → 0 < Tz k r z →
    Formalism.MainNotions.S.IsHaarOn (UWset k r z) μW → Formalism.MainNotions.S.IsHaarOn (Nset k r) μN →
    ∀ b : ℝ, 0 < b → 4 * bS k r < b → ∃ M : ℝ≥0∞, M < ∞ ∧ ∀ x ∈ UH (Hpk k r),
      (∫⁻ p : Mt k r × Mt k r, ENNReal.ofReal (gN (Matrix.of p.1 * Matrix.of p.2 * x) ^ (-b)) ∂(μW.prod μN)) ≤ M

theorem bS_le (k r : ℕ) : bS k r ≤ 2 * (r : ℝ) * ReciprocityTheory.ChartRestriction.DS.Mult1.nR k r ^ 2 := by
  have h : (2 * r + k) * (r * (2 * r + 2 * k + 1)) ≤ 2 * r * (2 * r + k + 1) ^ 2 := by
    nlinarith [Nat.zero_le (r * r * r), Nat.zero_le (r * r * k), Nat.zero_le (r * k * k), Nat.zero_le (k * k * k),
      Nat.zero_le (r * r), Nat.zero_le (r * k), Nat.zero_le (k * k), Nat.zero_le r, Nat.zero_le k]
  unfold bS dimN ReciprocityTheory.ChartRestriction.DS.Mult1.nR
  exact_mod_cast h

end ReciprocityTheory.ChartRestriction.DS.Mult1.S0
