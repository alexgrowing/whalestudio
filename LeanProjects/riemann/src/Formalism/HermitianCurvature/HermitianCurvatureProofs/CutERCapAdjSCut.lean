import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutERCapAdjCut

namespace Formalism.FourierDecayAlt.P.CutMP.ER

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants MeasureTheory
open scoped ComplexConjugate

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

noncomputable section

def wsAdj {k r : ℕ} (L : List (ℂ × List (B.Mat k r))) (b : B.Mat k r → ℂ) (x : B.Mat k r) : ℂ :=
  (L.map fun cw => conj cw.1 * (-1 : ℂ) ^ cw.2.length * B.Rw cw.2.reverse b x).sum

def CapAdjScalar : Prop :=
  ∀ (k r : ℕ) (Y : ℂ) (μ : Measure (Mt k r)), B.IsHaarOn (B.GV k r) μ → ∀ a b : B.Mat k r → ℂ,
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) a → HasCompactSupport a →
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) b → HasCompactSupport b →
    (∫ x : Mt k r, a (Matrix.of x) * star (wsAdj (capLw k r Y) b (Matrix.of x)) ∂μ) =
      ∫ x : Mt k r, a (Matrix.of x) * star (Q.CV k r (conj Y) b (Matrix.of x)) ∂μ

def CapAdjIntOfScalar : Prop := CapAdjScalar → CapAdjInt

end

end Formalism.FourierDecayAlt.P.CutMP.ER
