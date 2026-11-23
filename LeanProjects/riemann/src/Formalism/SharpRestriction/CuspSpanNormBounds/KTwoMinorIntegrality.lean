import Formalism.SharpRestriction.CuspSpanNormBounds.FrameFixingOrbitRelation
import Formalism.SharpRestriction.CuspSpanNormBounds.KappaEndpoints

noncomputable section

namespace Formalism.MainNotions.KTwoMinorIntegrality

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.Cnt

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def NormLB : Prop := ∀ (D : D7) (x : D.host.E), IsIntegral ℤ x → x ≠ 0 → 1 ≤ ∏ τ : D.what₂.Tau, ‖embS D τ x‖ ^ 2

def MinorInt : Prop := ∀ (D : D7) (X : TermTie D) (u : D.what₂.Word) (t : D.s.Term u u), LatticeIndexAndWeightTheory.FrameHyp X t →
  ∀ l, l ≤ D.R.rS → IsIntegral ℤ (Dl (X.fl t).fl (X.fl' t).fl l)

def LatSum : Prop := ∀ (ι : Type) [Fintype ι] (P : Finset (ι → ℂ)) (R : ℝ), 1 ≤ R →
  (∀ p ∈ P, ∀ q ∈ P, p ≠ q → 1 ≤ ∏ i, ‖p i - q i‖) →
  ∑ p ∈ P, ∏ i, (max 1 (‖p i‖ / R)) ^ (-(3 : ℝ)) ≤ (64 * R) ^ (2 * Fintype.card ι)

end Formalism.MainNotions.KTwoMinorIntegrality

end
