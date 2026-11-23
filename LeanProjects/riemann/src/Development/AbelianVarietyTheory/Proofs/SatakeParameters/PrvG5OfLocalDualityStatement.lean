import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ConclusionG5OfLocalDuality
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.HeckeCharEqOfLAdicRealisation
import ReciprocityTheory.Hypotheses.GalCoh
open Formalism.BasicNotions Formalism.ConjugateSelfDual Formalism.MainNotions Formalism.MainNotions.N Polynomial NumberField IsDedekindDomain ReciprocityTheory.Gal GlobalTheory.StringRepresentationDecomposition
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.conclusionG5_of_local_duality : LocalFiniteness → LocalTateDuality → LocalEulerChar → ∀ D : D7, SumRepresentations.admitted D → RbEx D → SumRepresentations.ConclusionG5 D := by
  first | exact @GlobalTheory.LevelPlaces.local_conditions_at_level | exact GlobalTheory.LevelPlaces.local_conditions_at_level | (intros; apply GlobalTheory.LevelPlaces.local_conditions_at_level <;> assumption)
