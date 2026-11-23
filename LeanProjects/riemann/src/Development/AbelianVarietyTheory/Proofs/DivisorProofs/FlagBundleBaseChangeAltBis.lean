import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFlagBundlePullFlag
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
theorem _root_.GlobalTheory.T.isFlagBundle_pullback' : ∀ (B Y B' : Scheme.{0}) (π : Y ⟶ B) (g : B' ⟶ B) (ι : Type) (E : ι → B.Modules) (r : ι → ℕ) (fl : ∀ a, Vert.Flag ((Scheme.Modules.pullback π).obj (E a)) (r a)), IsFlagBundle π E r fl → IsFlagBundle (Limits.pullback.snd π g) (fun a => (Scheme.Modules.pullback g).obj (E a)) r (fun a => GlobalTheory.FlagBaseChange.pullFlag π g (fl a)) := by
  first | exact @GlobalTheory.FlagBaseChange.isFlagBundle_pullFlag | exact GlobalTheory.FlagBaseChange.isFlagBundle_pullFlag | (intros; apply GlobalTheory.FlagBaseChange.isFlagBundle_pullFlag <;> assumption)
