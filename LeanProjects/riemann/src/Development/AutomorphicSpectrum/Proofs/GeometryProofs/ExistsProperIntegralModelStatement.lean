import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsProperIntegralModel
import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.CoordsAt
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.CompanionTheory.Ar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_proper_integral_model : ∀ (Ω : Type) [Field Ω] (o : Type) [CommRing o] [Algebra o Ω] (κ : Type) [Finite κ] (x : κ → Ω) (c₀ : κ), x c₀ ≠ 0 → (∀ a : Ω, ∃ g ∈ Algebra.adjoin o (Set.range fun j => x j / x c₀), ∃ h ∈ Algebra.adjoin o (Set.range fun j => x j / x c₀), h ≠ 0 ∧ a = g / h) → ∃ (X : Scheme.{0}) (ξ : Spec (CommRingCat.of Ω) ⟶ X) (s : X ⟶ Spec (CommRingCat.of o)), CoordTie o ξ x ∧ (∀ q : X, genPt ξ ⤳ q) ∧ IsIntegral X ∧ IsProper s ∧ ξ ≫ s = Spec.map (CommRingCat.ofHom (algebraMap o Ω)) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.exists_cl_scheme | exact GlobalTheory.CompanionTheory.Ar.exists_cl_scheme | (intros; apply GlobalTheory.CompanionTheory.Ar.exists_cl_scheme <;> assumption)
