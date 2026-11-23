import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIsoOfEpiVectorBundleSameRank
import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PoincareDeRhamDuality
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ZeroSectionBase
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsDeRhamSheafIffAlt
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ConjugateFiltration
open CategoryTheory AlgebraicGeometry Limits ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.DeRham GlobalTheory.DeRhamSheaf
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isIso_of_epi_vector_bundle_same_rank : ∀ {X : Scheme.{0}} {E E' : X.Modules} (π : E ⟶ E') [Epi π] (r : ℕ),
    GlobalTheory.VB.IsVB E r → GlobalTheory.VB.IsVB E' r → IsIso π := by
  first | exact @GlobalTheory.VB.isIso_of_epi_of_isVB | exact GlobalTheory.VB.isIso_of_epi_of_isVB | (intros; apply GlobalTheory.VB.isIso_of_epi_of_isVB <;> assumption)
