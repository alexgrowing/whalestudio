import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagBundlePullbackCoverIntegral
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
theorem _root_.GlobalTheory.T.flag_bundle_pullback_cover_integral : ∀ (k : Type) [CommRing k] (B Y : Scheme.{0}) [IsIntegral B] [IsIntegral Y] (q : B ⟶ Sp k) (p : Y ⟶ Sp k) (D : ℕ), IsArithVar q 1 → IsArithVar p D → ∀ (π : Y ⟶ B), π ≫ q = p → ∀ (ι : Type) [Fintype ι] (E : ι → B.Modules) (r : ι → ℕ), (∀ a, VB.IsVB (E a) (r a)) → ∀ (fl : ∀ a, Vert.Flag ((Scheme.Modules.pullback π).obj (E a)) (r a)), IsFlagBundle π E r fl → ∀ C : RegCover q, IsIntegral (Limits.pullback π C.ρ) ∧ IsArithVar (Limits.pullback.fst π C.ρ ≫ p) D ∧ π (genericPoint Y) = genericPoint B := by
  first | exact @GlobalTheory.FlagBundleCover.pullback_regCover_isArithVar | exact GlobalTheory.FlagBundleCover.pullback_regCover_isArithVar | (intros; apply GlobalTheory.FlagBundleCover.pullback_regCover_isArithVar <;> assumption)
