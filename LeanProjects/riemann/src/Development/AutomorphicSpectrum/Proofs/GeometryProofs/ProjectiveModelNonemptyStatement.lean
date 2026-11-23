import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ProjectiveModelNonempty
import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GlueApplyOfNotInFibre
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsGenericFlag
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.LatNormGrLatNeZeroOfSpan
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar NumberField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.projective_model_nonempty : ∀ (o : Type) [CommRing o] (Ω : Type) [Field Ω] [Algebra o Ω] (κ : Type) [Finite κ] (x : κ → Ω), (∃ c, x c ≠ 0 ∧ ∀ a : Ω, ∃ u ∈ chRing o x c, ∃ v ∈ chRing o x c, a = u / v) → Nonempty (PModel o x) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.nonempty_pModel_of_chart | exact GlobalTheory.CompanionTheory.Ar.nonempty_pModel_of_chart | (intros; apply GlobalTheory.CompanionTheory.Ar.nonempty_pModel_of_chart <;> assumption)
