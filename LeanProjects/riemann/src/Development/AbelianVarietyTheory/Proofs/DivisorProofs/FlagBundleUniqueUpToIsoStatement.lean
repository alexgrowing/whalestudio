import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagBundleUniqueUpToIso
import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ScholzeWeinsteinB
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsFlagBundleRankOne
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.RegularAlteration
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open scoped Classical
open Formalism.BasicNotions.DV Formalism.MainNotions.WeightThresholdDefs GlobalTheory.FlagAr GlobalTheory.ShFam.Pad GlobalTheory.VB
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flag_bundle_unique_up_to_iso : ∀ (B Y Y' : Scheme.{0}) (π : Y ⟶ B) (π' : Y' ⟶ B) (ι : Type) (E : ι → B.Modules) (r : ι → ℕ) (fl : ∀ a, GlobalTheory.Vert.Flag ((Scheme.Modules.pullback π).obj (E a)) (r a)) (fl' : ∀ a, GlobalTheory.Vert.Flag ((Scheme.Modules.pullback π').obj (E a)) (r a)), GlobalTheory.CovTest.IsFlagBundle π E r fl → GlobalTheory.CovTest.IsFlagBundle π' E r fl' → ∃ e : Y ≅ Y', e.hom ≫ π' = π := by
  first | exact @GlobalTheory.CovTest.exists_iso_of_isFlagBundle | exact GlobalTheory.CovTest.exists_iso_of_isFlagBundle | (intros; apply GlobalTheory.CovTest.exists_iso_of_isFlagBundle <;> assumption)
