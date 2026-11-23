import Mathlib
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsFiniteSplitTorusExtensionOfTorusExtension
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.GenericFiberGluing.SemistableCompleteSplit
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_finite_splitTorusExtension_of_torusExtension : ∀ (k : Type) [Field k] (G : Over (Spec (CommRingCat.of k))) [GrpObj G], Nonempty (TorusExt G) → ∃ (k' : Type) (_ : Field k') (_ : Algebra k k') (_ : FiniteDimensional k k'), Nonempty (TorusExtension (fieldBaseChange k k' G)) := by
  first | exact @GlobalTheory.SS.exists_finite_torusExtension_of_torusExt | exact GlobalTheory.SS.exists_finite_torusExtension_of_torusExt | (intros; apply GlobalTheory.SS.exists_finite_torusExtension_of_torusExt <;> assumption)
