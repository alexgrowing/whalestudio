import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SectionsFiniteFlatRankOfFiniteFlat
import Mathlib
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sections_finite_flat_rank_of_isFinite_flat : ∀ (X T : Scheme.{0}) (p : X ⟶ T) [IsFinite p] [Flat p] (r : ℕ), (∀ t, p.finrank t = r) → ∀ (U : T.Opens), IsAffineOpen U → letI := (p.app U).hom.toAlgebra; Module.Finite Γ(T, U) Γ(X, p ⁻¹ᵁ U) ∧ Module.Flat Γ(T, U) Γ(X, p ⁻¹ᵁ U) ∧ ∀ q : PrimeSpectrum Γ(T, U), Module.rankAtStalk Γ(X, p ⁻¹ᵁ U) q = r := by
  first | (exact @GlobalTheory.sections_finite_flat_rank_of_finite_flat) | (exact GlobalTheory.sections_finite_flat_rank_of_finite_flat) | (intros; apply GlobalTheory.sections_finite_flat_rank_of_finite_flat  <;> assumption)
