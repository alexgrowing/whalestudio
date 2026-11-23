import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsArithVarOfInt
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsFlagBundleRankOne
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.RegularAlteration
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BcFlag
open CategoryTheory AlgebraicGeometry Limits ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.CovTest GlobalTheory.Published
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_regular_integral_cover_same_dimension : RegularAlteration → ∀ (k : Type) [CommRing k] (Z : Scheme.{0}) [IsIntegral Z] (r : Z ⟶ Sp k) (d : ℕ),
    IsArithVar r d → ∃ (B' : Scheme.{0}) (_ : IsIntegral B') (ρ : B' ⟶ Z), IsArithVar (ρ ≫ r) d ∧
      (∀ b : B', IsRegularLocalRing (B'.presheaf.stalk b)) ∧ ρ (genericPoint B') = genericPoint Z ∧
      ρ.residueDegree (genericPoint B') ≠ 0 := by
  first | exact @GlobalTheory.AlterationOrder.regularAlteration_order | exact GlobalTheory.AlterationOrder.regularAlteration_order | (intros; apply GlobalTheory.AlterationOrder.regularAlteration_order <;> assumption)
