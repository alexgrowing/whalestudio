import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteAffineNeighbourhoodExists
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BcDensEqOfGram
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CxPts GlobalTheory.VB
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_affine_neighbourhood_exists : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) [IsIntegral X] (Y : Scheme.{0}) [IsIntegral Y] (q : Y ⟶ Sp k), IsArithVar p 1 → IsArithVar q 1 → ∀ (π : Y ⟶ X), π ≫ p = q → π (genericPoint Y) = genericPoint X → π.residueDegree (genericPoint Y) ≠ 0 → ∀ U₀ : X.Opens, genericPoint X ∈ U₀ → ∃ U : X.Opens, U ≤ U₀ ∧ IsAffineOpen U ∧ genericPoint X ∈ U ∧ IsAffineOpen (π ⁻¹ᵁ U) ∧ (π.app U).hom.Finite ∧ (π.app U).hom.Etale ∧ (letI := (π.app U).hom.toAlgebra; Module.finrank Γ(X, U) Γ(Y, π ⁻¹ᵁ U)) = π.residueDegree (genericPoint Y) := by
  first | exact @GlobalTheory.GenFiniteEtale.exists_finite_etale | exact GlobalTheory.GenFiniteEtale.exists_finite_etale | (intros; apply GlobalTheory.GenFiniteEtale.exists_finite_etale <;> assumption)
