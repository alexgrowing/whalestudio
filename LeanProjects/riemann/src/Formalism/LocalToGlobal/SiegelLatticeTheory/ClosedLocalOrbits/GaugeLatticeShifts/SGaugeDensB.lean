import Formalism.SharpRestriction.CuspSpanNormBounds.SGauge

open MeasureTheory Filter Topology
open scoped ENNReal

noncomputable section

namespace Formalism.MainNotions.S.Gauge

variable {n : ℕ}

abbrev EL (ε : Fin n → Bool) := EuclideanSpace ℝ (Fin (dimL ε))

def expC (ε : Fin n → Bool) (t : EL ε) : Formalism.REAL.UJ ε := expG ε ((obG ε).repr.symm t)

theorem uMat_expC (ε : Fin n → Bool) (t : EL ε) : uMat (expC ε t) = Matrix.of (thetaExp ε t) := by
  rw [expC, uMat_expG, of_thetaExp, linT_apply]

def jd (ε : Fin n → Bool) (t : EL ε) : ℝ≥0∞ := ENNReal.ofReal (chartJac (thetaExp ε) t)

def lamM (ε : Fin n → Bool) (s : ℝ) : Measure (Formalism.REAL.UJ ε) :=
  (((volume : Measure (EL ε)).restrict (Metric.ball 0 s)).withDensity (jd ε)).map (expC ε)

def ChartNhd (ε : Fin n → Bool) : Prop := ∀ s : ℝ, 0 < s → expC ε '' Metric.ball 0 s ∈ 𝓝 (1 : Formalism.REAL.UJ ε)

def TransC (ε : Fin n → Bool) : Prop :=
  ∃ s₀ : ℝ, 0 < s₀ ∧ ∀ s : ℝ, 0 < s → s ≤ s₀ → ∀ z : Formalism.REAL.UJ ε, ∃ U : Set (EL ε), IsOpen U ∧ ∃ φ : EL ε → EL ε,
    DifferentiableOn ℝ φ U ∧ (∀ t ∈ U, Matrix.of (thetaExp ε (φ t)) = uMat z * Matrix.of (thetaExp ε t)) ∧
    ∀ t ∈ Metric.ball (0 : EL ε) s, z * expC ε t ∈ expC ε '' Metric.ball 0 s → t ∈ U ∧ φ t ∈ Metric.ball (0 : EL ε) s

def JacInv (ε : Fin n → Bool) : Prop :=
  ∀ (U : Set (EL ε)) (φ : EL ε → EL ε) (Z : Matrix (Fin n) (Fin n) ℂ), IsOpen U → DifferentiableOn ℝ φ U →
    (∀ t ∈ U, Matrix.of (thetaExp ε (φ t)) = Z * Matrix.of (thetaExp ε t)) →
    ∀ t ∈ U, chartJac (thetaExp ε) (φ t) * |(fderiv ℝ φ t).det| = chartJac (thetaExp ε) t

def LocInv (ε : Fin n → Bool) (s : ℝ) : Prop :=
  ∀ (z : Formalism.REAL.UJ ε) (A : Set (Formalism.REAL.UJ ε)), MeasurableSet A → A ⊆ expC ε '' Metric.ball 0 s →
    (fun g => z * g) '' A ⊆ expC ε '' Metric.ball 0 s → lamM ε s ((fun g => z * g) '' A) = lamM ε s A

def LocInvOf (ε : Fin n → Bool) : Prop :=
  TransC ε → JacInv ε → ∃ s₀ : ℝ, 0 < s₀ ∧ ∀ s : ℝ, 0 < s → s ≤ s₀ → LocInv ε s

def BallForm (ε : Fin n → Bool) : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∃ s : ℝ, 0 < s ∧ ∀ ρ : ℝ, 0 < ρ → ρ ≤ s →
    Formalism.REAL.muG ε (expSet ε (Metric.ball (0 : gLie ε) ρ)) = ENNReal.ofReal c * ∫⁻ t in Metric.ball (0 : EL ε) ρ, jd ε t

def BallFormOf (ε : Fin n → Bool) : Prop :=
  ChartNhd ε → (∃ s₀ : ℝ, 0 < s₀ ∧ ∀ s : ℝ, 0 < s → s ≤ s₀ → LocInv ε s) → BallForm ε

def DensOfBall (ε : Fin n → Bool) : Prop := BallForm ε → GaugeDens ε

theorem gaugeDens_of_parts (ε : Fin n → Bool) (h1 : ChartNhd ε) (h2 : TransC ε) (h3 : JacInv ε) (h4 : LocInvOf ε)
    (h5 : BallFormOf ε) (h6 : DensOfBall ε) : GaugeDens ε :=
  h6 (h5 h1 (h4 h2 h3))

end Formalism.MainNotions.S.Gauge
