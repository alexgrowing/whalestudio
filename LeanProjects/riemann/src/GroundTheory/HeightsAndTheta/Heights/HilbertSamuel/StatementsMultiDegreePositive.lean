import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsDegreePositive
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR

noncomputable section

def MultiDegreePositive.Statement : Prop :=
  ∀ (F : Type) [Field F] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (q : Ideal (MRing ι F)) (e : ℕ), IsMultiProjPrime q →
    ringKrullDim (MRing ι F ⧸ q) = ((e + Fintype.card K : ℕ) : WithBot ℕ∞) →
    0 < intNum F q (fun _ : Fin e => fun _ : K => (1 : ℤ))

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
