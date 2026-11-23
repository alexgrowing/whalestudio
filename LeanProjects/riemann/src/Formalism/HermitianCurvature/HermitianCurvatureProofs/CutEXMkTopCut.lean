import Formalism.HermitianCurvature.HermitianCurvatureProofs.HermitianFormRankZeroApply
import Formalism.DoubleCosetMeasures.Statement

noncomputable section

open Matrix MeasureTheory
open scoped ContDiff

namespace Formalism.FourierDecayAlt.P.CutEXMT

open Formalism.FourierDecayAlt

def MkTopCut : Prop :=
  ∀ r : ℕ, ∃ β : (Fin r → Fin r → ℂ) → ℝ,
    ContDiffOn ℝ ∞ β {Z | (Matrix.of Z).det ≠ 0} ∧
    (∀ Z : Fin r → Fin r → ℂ, (Matrix.of Z).det ≠ 0 →
      Integrable (fun v : G.UT r → ℂ => β (Matrix.of.symm (Matrix.of Z * G.upper v))) ∧
        ∫ v : G.UT r → ℂ, β (Matrix.of.symm (Matrix.of Z * G.upper v)) = 1) ∧
    ∀ (X : Type) [TopologicalSpace X] (K : Set ((Fin r → Fin r → ℂ) × X)), IsCompact K →
      (∀ q ∈ K, (Matrix.of q.1).det ≠ 0) →
      ∃ K' : Set ((Fin r → Fin r → ℂ) × X), IsCompact K' ∧
        (∀ q ∈ K', (Matrix.of q.1).det ≠ 0 ∧ ∃ q₀ ∈ K, q.2 = q₀.2) ∧
        ∀ q : (Fin r → Fin r → ℂ) × X, (Matrix.of q.1).det ≠ 0 → β q.1 ≠ 0 →
          (∃ u : Matrix (Fin r) (Fin r) ℂ, Formalism.DoubleCosetMeasures.IsUpUni u ∧ (Matrix.of.symm (Matrix.of q.1 * u), q.2) ∈ K) →
          q ∈ K'

end Formalism.FourierDecayAlt.P.CutEXMT
