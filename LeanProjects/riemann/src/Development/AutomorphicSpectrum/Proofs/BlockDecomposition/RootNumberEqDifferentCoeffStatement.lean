import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RootNumberEqDifferentCoeff
import GroundTheory.GlobalFields.AnalyticClassNumber.HeckeContinued
import GroundTheory.GlobalFields.TateThesis.RootNumberLocalFinite
import GroundTheory.GlobalFields.IdeleGroups.ClassGroup
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PartialZetaFunctionalEquation
open NumberField GroundTheory.Global GroundTheory.Global.IdeleGroup
open scoped nonZeroDivisors
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.root_number_eq_different_coeff : ∀ (F : Type) [Field F] [NumberField F] (χ : HeckeCharacter F), standardOpenSubgroup F ≤ χ.toIdele.ker → χ.rootNumber = χ.coeff (differentIdeal ℤ (𝓞 F)) := by
  first | exact @GlobalTheory.CompanionTheory.PartialZeta.rootNumber_eq_coeff_different | exact GlobalTheory.CompanionTheory.PartialZeta.rootNumber_eq_coeff_different | (intros; apply GlobalTheory.CompanionTheory.PartialZeta.rootNumber_eq_coeff_different <;> assumption)
