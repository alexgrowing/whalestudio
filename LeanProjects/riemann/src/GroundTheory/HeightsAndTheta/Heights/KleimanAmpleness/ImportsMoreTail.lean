import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.IsMultiProjPrimeMIdealOverGraph
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (mIdealOver)

def GraphRestrict.Statement : Prop :=
  ∀ (k : Type) [Field k] (N : ℕ) (Ω : Type) [Field Ω] [Algebra k Ω] (x : Fin (N + 1) → Ω)
    (Q : Kleiman.LineBundle k x) (n : ℤ) (m : ℕ) (s : Fin m → Ω)
    (K' : Type) [Field K'] [Algebra k K'] (x' : Fin (N + 1) → K') (s' : Fin m → K')
    (hxy : ∀ i, x' i ≠ 0 → x i ≠ 0),
    IsGraphGen Q n s → mIdealOver k (graphVec x s) ≤ mIdealOver k (graphVec x' s') →
    (∃ i, x' i ≠ 0) → (∃ j, s' j ≠ 0) →
    ∃ (Q' : Kleiman.LineBundle k x') (r : Ω → K'),
      Kleiman.RestrictData Q.toSubSystem hxy Q'.toSubSystem r ∧ IsGraphGen Q' n s'

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
