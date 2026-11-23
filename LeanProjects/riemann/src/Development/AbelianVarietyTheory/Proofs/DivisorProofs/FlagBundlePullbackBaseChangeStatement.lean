import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagBundlePullbackBaseChange
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsFlagBundleRankOne
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.RegularAlteration
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BcFlag
open CategoryTheory AlgebraicGeometry Limits ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.CovTest GlobalTheory.Published
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flag_bundle_pullback_base_change : ∀ (B Y B' : Scheme.{0}) (π : Y ⟶ B) (g : B' ⟶ B) (ι : Type) (E : ι → B.Modules) (n : ι → ℕ)
    (fl : ∀ a, Vert.Flag ((Scheme.Modules.pullback π).obj (E a)) (n a)), IsFlagBundle π E n fl →
    IsFlagBundle (pullback.snd π g) (fun a => (Scheme.Modules.pullback g).obj (E a)) n (fun a => bcFlag π g (fl a)) := by
  first | exact @GlobalTheory.CovTest.BCFlag.isFlagBundle_baseChange | exact GlobalTheory.CovTest.BCFlag.isFlagBundle_baseChange | (intros; apply GlobalTheory.CovTest.BCFlag.isFlagBundle_baseChange <;> assumption)
