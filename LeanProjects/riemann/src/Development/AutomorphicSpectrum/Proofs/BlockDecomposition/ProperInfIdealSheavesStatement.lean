import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ProperInfIdealSheaves
import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PowSubSuccLe
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh GlobalTheory.CompanionTheory.GE
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.proper_inf_ideal_sheaves : ∀ {X S : Scheme.{0}} (f : X ⟶ S) [IsSeparated f] [LocallyOfFiniteType f] (T₁ T₂ : X.IdealSheafData), IsProper (T₁.subschemeι ≫ f) → IsProper (T₂.subschemeι ≫ f) → IsProper ((T₁ ⊓ T₂).subschemeι ≫ f) := by
  first | exact @GlobalTheory.CompanionTheory.GE.Union.isProper_inf | exact GlobalTheory.CompanionTheory.GE.Union.isProper_inf | (intros; apply GlobalTheory.CompanionTheory.GE.Union.isProper_inf <;> assumption)
