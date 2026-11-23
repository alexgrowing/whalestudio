import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.ComplexFibreIdealBot
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.GaussNormEqCoeffGaussNorm
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Geo (MRing PBlk IsArithVar ptsIntegral pot)

def ConeIntegralPts.Statement : Prop :=
  ∀ (n e : ℕ) (S : Matrix (Fin n) (Fin n) ℂ) (hS : IsUnit S) (P : Ideal (MRing (PBlk n)))
    (u : Fin n → ℂ),
    IsArithVar P (e + 1) → (∀ W ∈ (fundCycle (complexFibreIdeal P)).support, linForm u ∉ W) →
      cycleIntegral (ObjectsHeight.ofPointMatrix S hS) (fundCycle (complexFibreIdeal P)) e
          (fsLog (ObjectsHeight.ofPointMatrix S hS) u) =
        ptsIntegral P (pot fun _ : Fin e => IndefiniteRowSideFullHecke.ArithBezout.hermLine S hS)
          (IndefiniteRowSideFullHecke.ArithBezout.logFormNorm S hS u)

theorem mem_minimalPrimes_of_mem_fundCycle_support {n : ℕ} {J W : Ideal (MvPolynomial (Fin n) ℂ)}
    (hW : W ∈ (fundCycle J).support) : W ∈ J.minimalPrimes := by
  have h := Finsupp.support_onFinset_subset hW
  rwa [Set.Finite.mem_toFinset] at h

end GroundTheory.Heights₂.Heights
