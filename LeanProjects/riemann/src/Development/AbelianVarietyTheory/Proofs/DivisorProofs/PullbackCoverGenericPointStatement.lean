import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullbackCoverGenericPoint
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
theorem _root_.GlobalTheory.T.pullback_cover_generic_point : ∀ (k : Type) [CommRing k] (B Y : Scheme.{0}) [IsIntegral B] [IsIntegral Y] (q : B ⟶ Sp k) (π : Y ⟶ B), IsArithVar q 1 → π (genericPoint Y) = genericPoint B → ∀ (C : RegCover q) [IsIntegral (Limits.pullback π C.ρ)], (Limits.pullback.fst π C.ρ : (Limits.pullback π C.ρ : Scheme.{0}) ⟶ Y) (genericPoint (Limits.pullback π C.ρ : Scheme.{0})) = genericPoint Y ∧ (Limits.pullback.fst π C.ρ : (Limits.pullback π C.ρ : Scheme.{0}) ⟶ Y).residueDegree (genericPoint (Limits.pullback π C.ρ : Scheme.{0})) = C.deg := by
  first | exact @GlobalTheory.GenericBaseChange.baseChange_genericPoint_residueDegree | exact GlobalTheory.GenericBaseChange.baseChange_genericPoint_residueDegree | (intros; apply GlobalTheory.GenericBaseChange.baseChange_genericPoint_residueDegree <;> assumption)
