import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified
import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionUnramifiedOfHasGoodReductionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionUnramifiedImpTateModuleAndInfiniteStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InfiniteTorsionUnramifiedOfTateModuleUnramifiedStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.GoodReduction.HasGoodReductionOfInfiniteTorsionUnramified

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory

namespace UpperTheory.Lit.Nos.Nos
open GlobalTheory

theorem neronOggShafarevich : NeronOggShafarevichSt := by
  intro R K Ω _ _ _ _ _ _ _ _ _ _ V hV A _ _ hA
  tfae_have 1 → 2 := GlobalTheory.T.torsionUnramified_of_hasGoodReduction_alt R K Ω V hV A
  tfae_have 2 → 4 := fun hb => (GlobalTheory.T.torsionUnramified_imp_tateModule_and_infinite R K Ω V A hb).1
  tfae_have 2 → 3 := fun hb => (GlobalTheory.T.torsionUnramified_imp_tateModule_and_infinite R K Ω V A hb).2
  tfae_have 4 → 3 := by
    rintro ⟨l, hf, hl, ht⟩
    exact GlobalTheory.T.infinite_torsionUnramified_of_tateModuleUnramified R K Ω V hV A hA l hl ht
  tfae_have 3 → 1 := UpperTheory.Lit.Nos.C6.hasGoodReduction_of_infinite_torsionUnramified R K Ω V hV A hA
  tfae_finish

end UpperTheory.Lit.Nos.Nos
