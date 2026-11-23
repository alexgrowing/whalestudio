import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelTraitCharacterGroupFinrankLeGenusThree
import Development.AbelianVarietyTheory.Definitions.Divisors.ThetaSetupStructureMapComp
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.siegelTrait_characterGroup_finrank_le_genus_of_three_le : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)), 3 ≤ n → ∀ T : Trait F, Module.finrank ℤ T.D.toPre.X ≤ g := by
  first | exact @GlobalTheory.Poinc.Trait.finrank_le_of_three_le | exact GlobalTheory.Poinc.Trait.finrank_le_of_three_le | (intros; apply GlobalTheory.Poinc.Trait.finrank_le_of_three_le <;> assumption)
