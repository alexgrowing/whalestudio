import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianVarietySquareLinearEndomorphismFiniteLoca
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PsiMapFst
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AffineFiniteProjectiveRankAtStalk
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbelianSchemeGerms
open CategoryTheory MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AmpleGen
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.abelianVarietySquareLinearEndomorphism_finiteLocallyFree : ∀ (K : Type) [Field K] [IsAlgClosed K] (A : Over (Sp K)) [GrpObj A], IsAbelianScheme A → ∀ a₁ b₁ a₂ b₂ : ℤ, ((a₁ * b₂ - b₁ * a₂ : ℤ) : K) ≠ 0 → IsFinite (psiMap A a₁ b₁ a₂ b₂).left ∧ Flat (psiMap A a₁ b₁ a₂ b₂).left ∧ LocallyOfFinitePresentation (psiMap A a₁ b₁ a₂ b₂).left ∧ ∃ r : ℕ, (∀ y, (psiMap A a₁ b₁ a₂ b₂).left.finrank y = r) ∧ (r : K) ≠ 0 := by
  first | exact @GlobalTheory.AmpleGen.psiMap_finite_locallyFree | exact GlobalTheory.AmpleGen.psiMap_finite_locallyFree | (intros; apply GlobalTheory.AmpleGen.psiMap_finite_locallyFree <;> assumption)
