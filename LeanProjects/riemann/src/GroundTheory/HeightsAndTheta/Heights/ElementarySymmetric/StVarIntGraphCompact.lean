import Mathlib
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StVarIntGraph
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial
open GroundTheory.Heights₂.Heights (varInt SmoothNear euclPot contDiff_euclPot)
open GroundTheory.Heights₂.Heights.ComplexSets (zeroSet)
open scoped ContDiff

def VarIntGraphCompact.Statement : Prop :=
  ∀ (n e : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)) (p : MvPolynomial (Fin n) ℂ) (F : (Fin (n + 1) → ℂ) → ℝ)
    (Φ : Fin e → (Fin (n + 1) → ℂ) → ℝ),
    J.IsPrime → SmoothNear (zeroSet (graphIdeal J p)) F → HasCompactSupport F →
    (∀ k, SmoothNear (zeroSet (graphIdeal J p)) (Φ k)) →
      varInt (graphIdeal J p) e F Φ = varInt J e (fun x => F (graphPt p x)) (fun k x => Φ k (graphPt p x))

end GroundTheory.Heights₂.Heights.Targets
