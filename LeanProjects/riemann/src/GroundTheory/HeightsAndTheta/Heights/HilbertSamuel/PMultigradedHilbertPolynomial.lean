import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsHilbert
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsEventualPolynomial
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.AssemblyCN
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR

noncomputable section

universe u

theorem MultigradedHilbertPolynomial.proof (h : EventualPolynomial.Statement) :
    MultigradedHilbertPolynomial.Statement.{u} := by
  intro F _ K _ _ ι _ q d hq hdim
  have hlt : ringKrullDim (MRing ι F ⧸ q) < (((d + 1) + Fintype.card K : ℕ) : WithBot ℕ∞) := by
    rw [hdim]
    exact_mod_cast (by omega : d + Fintype.card K < d + 1 + Fintype.card K)
  have hdeg : DegLT (hilbFn q) (d + 1) :=
    HilbDegBound.full F K ι (d + 1) q hq.isPrime hq.multiHomog hlt
  exact h K d (hilbFn q) hdeg

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
