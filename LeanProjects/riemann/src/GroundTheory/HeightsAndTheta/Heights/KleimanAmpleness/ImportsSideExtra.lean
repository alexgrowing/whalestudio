import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.IsFieldSubalgebraSelf
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.Statements
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (secOver mIdealOver)

def SectionsPoly.Statement : Prop :=
  ∀ (F : Type) [Field F] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (Ω : Type) [Field Ω] [Algebra F Ω] (y : (Σ k, ι k) → Ω) (k₀ : K),
    IndefiniteRowSideFullHecke.Kleiman2.IsModelWithBase F y k₀ →
      ∃ P : MvPolynomial K ℚ, FieldNumbers.EventuallyPoly (NumbersDVR.hilbFn (mIdealOver F y)) P ∧
        ∀ β : K → ℤ, ∀ᶠ c : ℕ in Filter.atTop,
          (Module.finrank F (secOver F y (β + (c : ℤ) • IndefiniteRowSideFullHecke.Kleiman2.baseDeg k₀)) : ℚ) =
            eval (fun k => (((β + (c : ℤ) • IndefiniteRowSideFullHecke.Kleiman2.baseDeg k₀) k : ℤ) : ℚ)) P

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
