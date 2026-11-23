import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeSpecFieldSmoothOfRelativeDimension
import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.TateHonda
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.Et
open scoped TensorProduct DirectSum
open ReciprocityTheory.ChartRestriction.G.Semi
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.abelianScheme_specField_smoothOfRelativeDimension : ∀ (k : Type) [Field k] (A : Over (Spec (CommRingCat.of k))) [GrpObj A], IsAbelianScheme A → ∃ g : ℕ, SmoothOfRelativeDimension g A.hom := by
  first | (exact @GlobalTheory.AbFieldDim.exists_smoothOfRelativeDimension) | (exact GlobalTheory.AbFieldDim.exists_smoothOfRelativeDimension) | (intros; apply GlobalTheory.AbFieldDim.exists_smoothOfRelativeDimension  <;> assumption)
