import Mathlib
import GroundTheory.HeightsAndTheta.Heights.Intersections.RegLine
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

def PtsRegLimit.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Q : Ideal (MRing ι)) (e : ℕ)
    (M : Fin e → HermLine ι) (E : HermLine ι) (t : MRing ι)
    (ht : ∃ a : K → ℕ, (∀ k, E.a k = a k) ∧ IsMultiHomog t a),
    IsArithVar Q (e + 1) → (∀ j, IsSmoothHerm (M j)) → IsSmoothHerm E → t ∉ Q →
    Filter.Tendsto (fun ε => ptsIntegral Q (pot M) (fun z => Real.log ((regLine E t ht ε).h z)))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (ptsIntegral Q (pot M) (logNorm E t)))

end GroundTheory.Heights₂.Heights.Inter
