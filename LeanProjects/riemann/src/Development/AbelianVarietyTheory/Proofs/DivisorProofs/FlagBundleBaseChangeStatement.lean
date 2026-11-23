import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagBundleBaseChange
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
theorem _root_.GlobalTheory.T.flag_bundle_base_change : ∀ (B Y B' : Scheme.{0}) (π : Y ⟶ B) (ι : Type) (E : ι → B.Modules) (r : ι → ℕ) (fl : ∀ a, Vert.Flag ((Scheme.Modules.pullback π).obj (E a)) (r a)), IsFlagBundle π E r fl → ∀ g : B' ⟶ B, IsFlagBundle (Limits.pullback.snd π g) (fun a => (Scheme.Modules.pullback g).obj (E a)) r (fun a => FlagBaseChange.pullFlag π g (fl a)) := by
  first | exact @GlobalTheory.FlagBaseChangeStable.isFlagBundle_pullback | exact GlobalTheory.FlagBaseChangeStable.isFlagBundle_pullback | (intros; apply GlobalTheory.FlagBaseChangeStable.isFlagBundle_pullback <;> assumption)
