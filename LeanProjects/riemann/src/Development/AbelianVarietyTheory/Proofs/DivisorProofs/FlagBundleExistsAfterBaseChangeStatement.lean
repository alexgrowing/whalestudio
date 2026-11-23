import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagBundleExistsAfterBaseChange
import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ScholzeWeinsteinB
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsFlagBundleRankOne
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.RegularAlteration
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open scoped Classical
open Formalism.BasicNotions.DV Formalism.MainNotions.WeightThresholdDefs GlobalTheory.FlagAr GlobalTheory.ShFam.Pad GlobalTheory.VB
open CategoryTheory.Limits
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flag_bundle_exists_after_base_change : ∀ (B Y T : Scheme.{0}) (π : Y ⟶ B) (g : T ⟶ B) (ι : Type) [Fintype ι] (E : ι → B.Modules) (r : ι → ℕ) (fl : ∀ a, Vert.Flag ((Scheme.Modules.pullback π).obj (E a)) (r a)), IsFlagBundle π E r fl → ∃ fl' : ∀ a, Vert.Flag ((Scheme.Modules.pullback (pullback.snd π g)).obj ((Scheme.Modules.pullback g).obj (E a))) (r a), IsFlagBundle (pullback.snd π g) (fun a => (Scheme.Modules.pullback g).obj (E a)) r fl' := by
  first | exact @GlobalTheory.FlagBaseChange.isFlagBundle_pullback_snd | exact GlobalTheory.FlagBaseChange.isFlagBundle_pullback_snd | (intros; apply GlobalTheory.FlagBaseChange.isFlagBundle_pullback_snd <;> assumption)
