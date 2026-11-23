import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.QuadraticFormPositiveNearCompact
import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MemSupportBDIff
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsExphOnEmpty
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocMapOfMem
open CategoryTheory AlgebraicGeometry Limits NumberField IsDedekindDomain Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.CxPts GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Mean4O GlobalTheory.ChernReg
open scoped TensorProduct ContDiff

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.quadratic_form_positive_near_compact : ∀ (d : ℕ) (C U : Set (ReciprocityTheory.L2DbarEstimates.V d)) (f : ReciprocityTheory.L2DbarEstimates.V d × ReciprocityTheory.L2DbarEstimates.V d → ReciprocityTheory.L2DbarEstimates.V d) (q : ReciprocityTheory.L2DbarEstimates.V d → ReciprocityTheory.L2DbarEstimates.V d → ℝ), IsCompact C → IsOpen U → C ⊆ U → Continuous f → (∀ z ∈ C, f (z, 0) = z) → ContinuousOn (fun x : ReciprocityTheory.L2DbarEstimates.V d × ReciprocityTheory.L2DbarEstimates.V d => q x.1 x.2) (C ×ˢ Set.univ) → (∀ z ∈ C, ∀ (t : ℝ) η, q z (t • η) = t ^ 2 * q z η) → (∀ z ∈ C, ∀ η, η ≠ 0 → 0 < q z η) → ∃ ε, 0 < ε ∧ ∀ z ∈ C, ∀ η, q z η < ε → f (z, η) ∈ U := by
  first | exact @GlobalTheory.shortRadius_of_fixes_zero_section | exact GlobalTheory.shortRadius_of_fixes_zero_section | (intros; apply GlobalTheory.shortRadius_of_fixes_zero_section <;> assumption)
