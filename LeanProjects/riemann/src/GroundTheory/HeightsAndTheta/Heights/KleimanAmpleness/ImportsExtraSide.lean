import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.IsFieldSubalgebraSelf
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.IsMultiProjPrimeMIdealOverGraph
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (cechHc quotPart mIdealOver)

def MultiSerre.Statement : Prop :=
  ∀ (F : Type) [Field F] (K : Type) [Fintype K] [LinearOrder K] (ι : K → Type) [∀ k, Fintype (ι k)]
    [∀ k, LinearOrder (ι k)] (V : Ideal (MvPolynomial (Σ k, ι k) F)),
    NumbersDVR.IsMultiHomogIdeal V →
      ∀ᶠ m : K → ℤ in Filter.atTop,
        (∀ i : ℕ, 1 ≤ i → Subsingleton (cechHc ι (quotPart F V) m i)) ∧
        (Module.finrank F (cechHc ι (quotPart F V) m 0) : ℤ) = NumbersDVR.hilbFn V m

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
