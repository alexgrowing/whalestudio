import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.RegAtLeIffSpecializes
import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GlueApplyOfNotInFibre
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsGenericFlag
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.LatNormGrLatNeZeroOfSpan
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar NumberField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.regAt_le_iff_specializes : ∀ (o : Type) [CommRing o] (Ω : Type) [Field Ω] [Algebra o Ω] (κ : Type) [Finite κ] (x : κ → Ω) (M : PModel o x) (p q : Cpt M.ξ), regAt M.ξ p ≤ regAt M.ξ q ↔ q.1 ⤳ p.1 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.regAt_le_regAt_iff_specializes | exact GlobalTheory.CompanionTheory.Ar.regAt_le_regAt_iff_specializes | (intros; apply GlobalTheory.CompanionTheory.Ar.regAt_le_regAt_iff_specializes <;> assumption)
