import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeOfCountableHolomorphicImagesCover
import Development.AbelianVarietyTheory.Definitions.Divisors.IsHolPeriods
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PELU
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.le_of_countable_holomorphic_images_cover_open : ∀ (d d' : ℕ) (K : Type) [Countable K] (U : K → Set (Fin d → ℂ)) (f : K → (Fin d → ℂ) → (Fin d' → ℂ)) (W : Set (Fin d' → ℂ)), (∀ i, IsOpen (U i)) → (∀ i, DifferentiableOn ℂ (f i) (U i)) → IsOpen W → W.Nonempty → W ⊆ ⋃ i, f i '' U i → d' ≤ d := by
  first | exact @GlobalTheory.le_of_countable_holomorphic_images_cover | exact GlobalTheory.le_of_countable_holomorphic_images_cover | (intros; apply GlobalTheory.le_of_countable_holomorphic_images_cover <;> assumption)
