import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.CongruenceAtSplitFrobeniusHolds
import Formalism.HermitianCurvature.WeylElementCommutesLevelOne

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal

namespace Formalism.L2.SG.Pf

open Formalism.QuantumDeterminants

variable {k r : ℕ}

def expBall (S : Set (Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)) (ρ : ℝ) : Set (Mt k r) :=
  (fun x : Formalism.MainNotions.S.lieE S =>
      fun i j => NormedSpace.exp (Formalism.MainNotions.S.unrealify (x : EuclideanSpace ℝ _)) i j) '' Metric.ball 0 ρ

def IsGaugeOn (S : Set (Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)) (μ : Measure (Mt k r)) : Prop :=
  Formalism.MainNotions.S.IsHaarOn S μ ∧
    Tendsto (fun ρ : ℝ => (μ (expBall S ρ)).toReal / (volume (Metric.ball (0 : Formalism.MainNotions.S.lieE S) ρ)).toReal)
      (𝓝[>] 0) (𝓝 1)

def GaugeExists : Prop :=
  ∀ k r : ℕ, (∃ μ : Measure (Mt k r), IsGaugeOn (UH (Hpk k r)) μ) ∧
    ∃ μ : Measure (Mt k r), IsGaugeOn (Formalism.FourierDecayAlt.B2.UWb k r) μ

def BruhatHaar : Prop :=
  ∀ (k r : ℕ) (μ μb : Measure (Mt k r)), IsGaugeOn (UH (Hpk k r)) μ → IsGaugeOn (Formalism.FourierDecayAlt.B2.UWb k r) μb →
    ∀ φ : Mt k r → ℝ≥0∞, Measurable φ →
      ∫⁻ x, φ x ∂μ = ENNReal.ofReal (2 ^ r) * ∫⁻ c : Fin r → ℂ, ENNReal.ofReal (Formalism.FourierDecayAlt.B2.cWeight k r c) *
        ∫⁻ n, ∫⁻ m, ∫⁻ n', φ (fun i j => (Matrix.of n * bigCell k r c 1 * Matrix.of m * (Matrix.of n')⁻¹) i j)
          ∂(Formalism.MainNotions.S.haarLie (Nset k r) 1) ∂μb ∂(Formalism.MainNotions.S.haarLie (Nset k r) 1)

def wbConst (k : ℕ) (T T' a a' : ℝ) : ℝ :=
  2 * Formalism.MainNotions.S.UnitaryVolumeMass.volU k ^ 2 / ((T * T') ^ k * Formalism.MainNotions.S.UnitaryVolumeMass.volU (k - 1) * a * a')

def WbHaar : Prop :=
  ∀ (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ), 1 ≤ k → inWb k r z → inWb k r z' → 0 < Tz k r z → 0 < Tz k r z' →
    ∀ μb μW μW' : Measure (Mt k r), IsGaugeOn (Formalism.FourierDecayAlt.B2.UWb k r) μb →
    Formalism.MainNotions.S.IsHaarOn (UWset k r z) μW → Formalism.MainNotions.S.IsHaarOn (UWset k r z') μW' →
    ∀ a a' : ℝ, 0 < a → 0 < a' → μW Set.univ = ENNReal.ofReal a → μW' Set.univ = ENNReal.ofReal a' →
    ∀ μsec, IsSection k r z z' μsec → ∀ φ : Mt k r → ℝ≥0∞, Measurable φ →
      ∫⁻ m, φ m ∂μb = ENNReal.ofReal (wbConst k (Tz k r z) (Tz k r z') a a') *
        ∫⁻ ζ : ℂ, ENNReal.ofReal (Formalism.FourierDecayAlt.B2.zWeight k (Tz k r z) (Tz k r z') ζ) *
          ∫⁻ h, ∫⁻ h', φ (fun i j => (Matrix.of h * Formalism.FourierDecayAlt.B2.embWb k r (μsec ζ) * (Matrix.of h')⁻¹) i j) ∂μW' ∂μW

def DisintG (μ μW μW' μN : Measure (Mt k r)) (T T' : ℝ) (μsec : ℂ → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) (K : ℝ) :
    Prop :=
  ∀ φ : Mt k r → ℝ≥0∞, Measurable φ →
    ∫⁻ x, φ x ∂μ = ENNReal.ofReal K * ∫⁻ q : (Fin r → ℂ) × ℂ,
      ENNReal.ofReal (bcWeight k r T T' q) *
        ∫⁻ s, ∫⁻ s', φ (fun i j => (Matrix.of s * bigCell k r q.1 (μsec q.2) * (Matrix.of s')⁻¹) i j)
          ∂(Formalism.MainNotions.S.muS μW' μN) ∂(Formalism.MainNotions.S.muS μW μN)

def jacConst (k r : ℕ) (T T' a a' κ : ℝ) : ℝ :=
  2 ^ (r + 1) * Formalism.MainNotions.S.UnitaryVolumeMass.volU k ^ 2 / ((T * T') ^ k * Formalism.MainNotions.S.UnitaryVolumeMass.volU (k - 1) * a * a' * κ ^ 2)

def JacGauge : Prop :=
  ∀ (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ), 1 ≤ k → inWb k r z → inWb k r z' → 0 < Tz k r z → 0 < Tz k r z' →
    ∀ μ μW μW' : Measure (Mt k r), IsGaugeOn (UH (Hpk k r)) μ →
    Formalism.MainNotions.S.IsHaarOn (UWset k r z) μW → Formalism.MainNotions.S.IsHaarOn (UWset k r z') μW' →
    ∀ a a' : ℝ, 0 < a → 0 < a' → μW Set.univ = ENNReal.ofReal a → μW' Set.univ = ENNReal.ofReal a' →
    ∀ κ : ℝ, 0 < κ → ∀ μsec, IsSection k r z z' μsec →
      DisintG μ μW μW' (Formalism.MainNotions.S.haarLie (Nset k r) (ENNReal.ofReal κ)) (Tz k r z) (Tz k r z') μsec
        (jacConst k r (Tz k r z) (Tz k r z') a a' κ)

end Formalism.L2.SG.Pf
