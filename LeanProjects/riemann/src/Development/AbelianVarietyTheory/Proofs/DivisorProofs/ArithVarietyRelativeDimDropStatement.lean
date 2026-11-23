import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithVarietyRelativeDimDrop
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsFlagBundleRankOne
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.RegularAlteration
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.arith_variety_relative_dim_drop : ∀ (k : Type) [CommRing k] (Y Y₁ : Scheme.{0}) (p : Y ⟶ Sp k) (q₁ : Y₁ ⟶ Sp k) (ρ : Y ⟶ Y₁) (D : ℕ),
    ρ ≫ q₁ = p → IsArithVar p D → IsIntegral Y₁ → IsProjOver q₁ → Surjective ρ →
    topologicalKrullDim Y = topologicalKrullDim Y₁ + 1 → ∃ d₁ : ℕ, D = d₁ + 1 ∧ IsArithVar q₁ d₁ := by
  first | exact @GlobalTheory.isArithVar_of_surjective_dim_succ | exact GlobalTheory.isArithVar_of_surjective_dim_succ | (intros; apply GlobalTheory.isArithVar_of_surjective_dim_succ <;> assumption)
