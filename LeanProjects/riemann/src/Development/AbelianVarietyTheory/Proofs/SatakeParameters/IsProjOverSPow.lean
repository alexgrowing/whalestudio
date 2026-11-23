import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.HeckePowOne
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CoordValuationBoundLocal
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.PowerOfAbelianSchemeProjective
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.WeightTwoHeckePower

namespace GlobalTheory.WeightTwoHeckePower

theorem isProjOver_sPow : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p), D.CompactB → ∀ (gb : GBase D.toG ℂ) (N : ℕ), 3 ≤ N →
    N.Coprime p → ∀ (X : GenModel gb N) (r : ℕ), IsProjOver (sPow X r) := by
  intro p _ D hC gb N hN hNp X r
  have hX : IsProjOver X.s := GlobalTheory.UPel.HT.GenProj.isProjOver_genModel p D hC gb N hN hNp X
  exact GlobalTheory.KS.isProjOver_pow ℂ X.X X.s hX X.univ.A X.univ.ab _
    (LB.isLB_pull X.univ.isLB _) X.univ.ample r

end GlobalTheory.WeightTwoHeckePower
