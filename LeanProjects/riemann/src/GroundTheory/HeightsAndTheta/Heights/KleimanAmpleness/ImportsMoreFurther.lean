import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.IsFieldSubalgebraSelf
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.IsMultiProjPrimeMIdealOverGraph
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (cechHc quotPart mIdealOver)

def EulerPoly.Statement : Prop :=
  ∀ (F : Type) [Field F] (K : Type) [Fintype K] [LinearOrder K] (ι : K → Type) [∀ k, Fintype (ι k)]
    [∀ k, LinearOrder (ι k)] (V : Ideal (MvPolynomial (Σ k, ι k) F)),
    NumbersDVR.IsMultiHomogIdeal V →
      ∃ (B : ℕ) (χ : MvPolynomial K ℚ),
        (∀ (m : K → ℤ) (i : ℕ), FiniteDimensional F (cechHc ι (quotPart F V) m i)) ∧
        (∀ (m : K → ℤ) (i : ℕ), B < i → Subsingleton (cechHc ι (quotPart F V) m i)) ∧
        ∀ m : K → ℤ, ∑ i ∈ Finset.range (B + 1),
          (-1 : ℚ) ^ i * (Module.finrank F (cechHc ι (quotPart F V) m i) : ℚ) =
            eval (fun k => (m k : ℚ)) χ

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
