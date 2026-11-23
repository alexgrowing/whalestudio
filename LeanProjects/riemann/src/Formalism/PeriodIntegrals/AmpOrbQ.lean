import Formalism.SharpRestriction.CuspSpanNormBounds.RootMeasBig

open MeasureTheory
open scoped ENNReal

noncomputable section

namespace PI.AmpOrbQ

open Formalism.BasicNotions Formalism.QuantumDeterminants Formalism.MainNotions.S

def OrbQuotEx : Prop :=
  ∀ (k r : ℕ) (L : LocBessel k r) (p : Point ℂ (r + 1)) (g₀ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)
    (μR : Measure (Mt k r)), IsPtRepO L p g₀ → 0 < Gf k r L.z L.z' g₀ → IsHaarOn (RStab k r g₀) μR →
    ∃ ν : Measure (PairSp k r), IsOrbQuot L g₀ μR ν

def HaarLieN : Prop :=
  ∀ (k r : ℕ) (κ : ℝ≥0∞), κ ≠ 0 → κ ≠ ⊤ →
    Formalism.MainNotions.S.IsHaarOn (Formalism.QuantumDeterminants.Nset k r) (Formalism.MainNotions.S.haarLie (Formalism.QuantumDeterminants.Nset k r) κ)

end PI.AmpOrbQ
