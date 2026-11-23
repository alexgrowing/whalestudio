import Mathlib
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.GraphIdeal
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial MeasureTheory
open GroundTheory.Heights₂.Heights (varInt SmoothNear chartAbsDens)
open GroundTheory.Heights₂.Heights.ComplexSets (zeroSet IsFiniteProjection)

def VarIntGraphInt.Statement : Prop :=
  ∀ (n e : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)) (p : MvPolynomial (Fin n) ℂ) (F : (Fin (n + 1) → ℂ) → ℝ)
    (Φ : Fin e → (Fin (n + 1) → ℂ) → ℝ),
    J.IsPrime → SmoothNear (zeroSet (graphIdeal J p)) F → (∀ k, SmoothNear (zeroSet (graphIdeal J p)) (Φ k)) →
    (∀ B : Matrix (Fin e) (Fin (n + 1)) ℂ, IsFiniteProjection (graphIdeal J p) B →
      Integrable (chartAbsDens (graphIdeal J p) B F Φ)) →
      varInt (graphIdeal J p) e F Φ = varInt J e (fun x => F (graphPt p x)) (fun k x => Φ k (graphPt p x))

end GroundTheory.Heights₂.Heights.Targets
