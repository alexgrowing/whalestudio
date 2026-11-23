import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagBundleGluesFromCover
import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ScholzeWeinsteinB
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsFlagBundleRankOne
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.RegularAlteration
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullFlag
open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open scoped Classical
open Formalism.BasicNotions.DV Formalism.MainNotions.WeightThresholdDefs GlobalTheory.FlagAr GlobalTheory.ShFam.Pad GlobalTheory.VB

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flag_bundle_glues_from_cover : ∀ (B : Scheme.{0}) (ι : Type) [Fintype ι] (E : ι → B.Modules) (r : ι → ℕ), (∀ a, GlobalTheory.VB.IsVB (E a) (r a)) → (∀ x : B, ∃ U : B.Opens, x ∈ U ∧ ∃ (Y : Scheme.{0}) (π : Y ⟶ U.toScheme) (fl : ∀ a, Vert.Flag ((Scheme.Modules.pullback π).obj ((Scheme.Modules.pullback U.ι).obj (E a))) (r a)), IsFlagBundle π (fun a => (Scheme.Modules.pullback U.ι).obj (E a)) r fl) → ∃ (Y : Scheme.{0}) (π : Y ⟶ B) (fl : ∀ a, Vert.Flag ((Scheme.Modules.pullback π).obj (E a)) (r a)), IsFlagBundle π E r fl := by
  first | exact @GlobalTheory.FlagGlue.exists_isFlagBundle_of_cover | exact GlobalTheory.FlagGlue.exists_isFlagBundle_of_cover | (intros; apply GlobalTheory.FlagGlue.exists_isFlagBundle_of_cover <;> assumption)
