import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagBundleProductOfEach
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
theorem _root_.GlobalTheory.T.flag_bundle_product_of_each : ∀ (k : Type) [CommRing k] (B : Scheme.{0}) (q : B ⟶ Sp k) (ι : Type) [Fintype ι] (E : ι → B.Modules) (r : ι → ℕ), IsProjOver q → (∀ a, ∃ (Y : Scheme.{0}) (π : Y ⟶ B) (fl : ∀ _ : Unit, GlobalTheory.Vert.Flag ((Scheme.Modules.pullback π).obj (E a)) (r a)), GlobalTheory.CovTest.IsFlagBundle π (fun _ : Unit => E a) (fun _ => r a) fl ∧ IsProjOver (π ≫ q)) → ∃ (Y : Scheme.{0}) (π : Y ⟶ B) (fl : ∀ a, GlobalTheory.Vert.Flag ((Scheme.Modules.pullback π).obj (E a)) (r a)), GlobalTheory.CovTest.IsFlagBundle π E r fl ∧ IsProjOver (π ≫ q) := by
  first | exact @GlobalTheory.FlagFamily.exists_isFlagBundle_isProjOver | exact GlobalTheory.FlagFamily.exists_isFlagBundle_isProjOver | (intros; apply GlobalTheory.FlagFamily.exists_isFlagBundle_isProjOver <;> assumption)
