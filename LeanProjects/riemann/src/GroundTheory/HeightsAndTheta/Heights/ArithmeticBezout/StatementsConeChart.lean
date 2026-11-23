import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.MemMinimalPrimesOfMemFundCycleSupport
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterGood
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Geo (MRing PBlk IsArithVar IsGoodProj ptsIntegralAt pot)

def ConeIntegralChart.Statement : Prop :=
  ∀ (n e : ℕ) (S : Matrix (Fin n) (Fin n) ℂ) (hS : IsUnit S) (P : Ideal (MRing (PBlk n)))
    (u : Fin n → ℂ) (Ψ : (((k : Unit) → PBlk n k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)),
    IsArithVar P (e + 1) → (∀ W ∈ (fundCycle (complexFibreIdeal P)).support, linForm u ∉ W) →
      IsGoodProj P Ψ →
      coneIntegral (ObjectsHeight.ofPointMatrix S hS) (complexFibreIdeal P) e
          (fsLog (ObjectsHeight.ofPointMatrix S hS) u) =
        ptsIntegralAt P Ψ (pot fun _ : Fin e => IndefiniteRowSideFullHecke.ArithBezout.hermLine S hS)
          (IndefiniteRowSideFullHecke.ArithBezout.logFormNorm S hS u)

end GroundTheory.Heights₂.Heights
