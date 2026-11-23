import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemPrimitiveDeRhamCohomologyOfAdditivePeriods
import Development.AbelianVarietyTheory.Definitions.Divisors.IsRatioCover
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.CechDR GlobalTheory.CechPer
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_primitiveDeRhamCohomology_of_additive_periods : ∀ (A : Over (Sp ℂ)) [GrpObj A] (g : ℕ) (L : LB A.left) (u : HolUnif A L g), IsAbelianScheme A → ∀ (c : FirstDeRham (str A)) (p : u.Λ →+ ℂ), IsPer u.ex u.Λ (cmp1 (str A) c) p → c ∈ primDR A := by
  first | exact @GlobalTheory.CechPer.mem_primDR_of_isPer | exact GlobalTheory.CechPer.mem_primDR_of_isPer | (intros; apply GlobalTheory.CechPer.mem_primDR_of_isPer <;> assumption)
