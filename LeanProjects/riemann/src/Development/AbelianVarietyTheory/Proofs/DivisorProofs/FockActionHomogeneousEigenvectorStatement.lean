import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockActionHomogeneousEigenvector
import Formalism.LocalRingCardinality.DataTheta
open Formalism.BasicNotions.TH
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fock_action_homogeneous_eigenvector : ∀ (P Q R S : ℕ) (x : ℚ) (e e₀ : ℕ) (f g : Formalism.BasicNotions.TH.Pol P Q R S),
    f ∈ Formalism.BasicNotions.TH.homog (Formalism.BasicNotions.TH.Ln P Q R S) e →
    (∀ Y : Formalism.BasicNotions.TH.Mat P Q, Formalism.BasicNotions.TH.IsKC Y → Formalism.BasicNotions.TH.fockAct1 P Q R S Y f = ((x : ℂ) * Y.trace) • f) →
    g ≠ 0 → g ∈ Formalism.BasicNotions.TH.homog (Formalism.BasicNotions.TH.Ln P Q R S) e₀ →
    (∀ Y : Formalism.BasicNotions.TH.Mat P Q, Formalism.BasicNotions.TH.IsKC Y → Formalism.BasicNotions.TH.fockAct1 P Q R S Y g = ((x : ℂ) * Y.trace) • g) →
    e₀ < e →
    f ∈ Submodule.span ℂ {f' | ∃ Z : Formalism.BasicNotions.TH.Mat R S, Formalism.BasicNotions.TH.IsPC Z ∧
      ∃ g' ∈ Formalism.BasicNotions.TH.homog (Formalism.BasicNotions.TH.Ln P Q R S) (e - 2),
        (∀ Y : Formalism.BasicNotions.TH.Mat P Q, Formalism.BasicNotions.TH.IsKC Y → Formalism.BasicNotions.TH.fockAct1 P Q R S Y g' = ((x : ℂ) * Y.trace) • g') ∧
        f' = Formalism.BasicNotions.TH.plusPart (Formalism.BasicNotions.TH.fockAct2 P Q R S Z) g'} := by
  first | exact @GlobalTheory.FockScalarType.mem_span_raising | exact GlobalTheory.FockScalarType.mem_span_raising | (intros; apply GlobalTheory.FockScalarType.mem_span_raising <;> assumption)
