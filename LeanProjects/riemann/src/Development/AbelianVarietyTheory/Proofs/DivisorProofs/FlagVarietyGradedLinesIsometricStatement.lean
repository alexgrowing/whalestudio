import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagVarietyGradedLinesIsometric
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsFlagBundleRankOne
import Development.AbelianVarietyTheory.Definitions.Divisors.NormSqColGrLineOfOrthogonal
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.RegularAlteration
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ArBirational
open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flag_variety_graded_lines_isometric : ∀ (ι : Type) [Fintype ι] (N : ℕ), ∃ (E : ι → (Sp ℤ).Modules) (h : ∀ a, VMetric (𝟙 (Sp ℤ)) (E a) N) (H : ∀ a, (h a).IsCInf) (fl : ∀ a, GlobalTheory.Vert.Flag ((Scheme.Modules.pullback (GlobalTheory.FlagZ.flStr ι N)).obj (E a)) N), IsFlagBundle (GlobalTheory.FlagZ.flStr ι N) E (fun _ => N) fl ∧ ∀ (a : ι) (i : Fin N), (VMetric.grLB (fl a) i ((H a).pull (GlobalTheory.FlagZ.flStr ι N) (Category.comp_id _))).Isometric (GlobalTheory.FlagZ.grLine (a, i)) := by
  first | exact @GlobalTheory.FlagZ.Taut.isFlagBundle_std_isometric | exact GlobalTheory.FlagZ.Taut.isFlagBundle_std_isometric | (intros; apply GlobalTheory.FlagZ.Taut.isFlagBundle_std_isometric <;> assumption)
