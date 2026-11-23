import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSmulOfRankOne
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.PointShiftSt
import Development.AbelianVarietyTheory.Definitions.Divisors.HtValOnSubset
open AlgebraicGeometry CategoryTheory NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory GlobalTheory GlobalTheory.CM GlobalTheory.FlatCM
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_smul_of_rank_one' : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H), D.p + D.q = 1 → ∀ γ : D.La →+ D.La, (∀ (s : 𝓞 E) (x : D.La), γ (s • x) = s • γ x) → ∃ g : 𝓞 E, ∀ x, γ x = g • x := by
  first | exact @GlobalTheory.FlatCM.exists_smul_of_rank_one | exact GlobalTheory.FlatCM.exists_smul_of_rank_one | (intros; apply GlobalTheory.FlatCM.exists_smul_of_rank_one <;> assumption)
