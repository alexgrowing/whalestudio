import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RegularCoversCommonRefinement
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsFlagBundleRankOne
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.RegularAlteration
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRegularCoverOfAlterationStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullFlag
open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.regular_covers_common_refinement : RegularAlteration → ∀ (k : Type) [CommRing k] (B : Scheme.{0}) [IsIntegral B] (q : B ⟶ Sp k), IsArithVar q 1 → ∀ C₁ C₂ : RegCover q, ∃ C : RegCover q, (∃ t₁ : C.Y ⟶ C₁.Y, t₁ ≫ C₁.ρ = C.ρ) ∧ ∃ t₂ : C.Y ⟶ C₂.Y, t₂ ≫ C₂.ρ = C.ρ := by
  first | exact @GlobalTheory.RegCoverCommon.exists_regCover_le_both | exact GlobalTheory.RegCoverCommon.exists_regCover_le_both | (intros; apply GlobalTheory.RegCoverCommon.exists_regCover_le_both <;> assumption)
