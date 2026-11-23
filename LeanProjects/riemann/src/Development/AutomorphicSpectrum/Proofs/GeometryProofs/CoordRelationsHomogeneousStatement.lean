import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.CoordRelationsHomogeneous
import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.EmbedsGeneric
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.GoodOrigin
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.SmallPointsCoordRatioBoundStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coord_relations_homogeneous : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] [CharZero Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (k₀ : K), CoordTie ℤ ξ (fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩) → EmbedsGeneric ξ (fun i : J k₀ => y ⟨k₀, i⟩) → ∀ k : K, ∃ (l : ℕ) (n : Fin l → ℕ) (F : Fin l → J k → MvPolynomial (J k₀) ℤ), (∀ t j, (F t j).IsHomogeneous (n t)) ∧ (∀ t j j', MvPolynomial.aeval (fun i' : J k₀ => y ⟨k₀, i'⟩) (F t j) * y ⟨k, j'⟩ = MvPolynomial.aeval (fun i' : J k₀ => y ⟨k₀, i'⟩) (F t j') * y ⟨k, j⟩) ∧ ∀ (L : Type) [Field L] [CharZero L] (z : (Σ k, J k) → L), z ∈ Small.ptsOver L (mCoordIdeal y) → ∃ t j, MvPolynomial.aeval (fun i' : J k₀ => z ⟨k₀, i'⟩) (F t j) ≠ 0 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.FormFamilies.finite_families | exact GlobalTheory.CompanionTheory.Ar.FormFamilies.finite_families | (intros; apply GlobalTheory.CompanionTheory.Ar.FormFamilies.finite_families <;> assumption)
