import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HodgeLineBundleEighthPowerIsoPow
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.IsE8ThetaStructure
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hodgeLineBundle_eighthPower_iso_pow : ∀ (S : Scheme.{0}) (G H : Over S) [GrpObj G] [GrpObj H] (g : ℕ) (pr : Fin 8 → (H ⟶ G)), (∀ u, IsMonHom (pr u)) → (∀ (T : Over S) (y : Fin 8 → (T ⟶ G)), ∃! x : T ⟶ H, ∀ u, x ≫ pr u = y u) → IsSemiAbelian G → SmoothOfRelativeDimension g G.hom → LBIso (GlobalTheory.SiegelTor.hodge H (8 * g)) (lbPow (GlobalTheory.SiegelTor.hodge G g) 8) := by
  first | exact @GlobalTheory.HodgePow.hodge_eight_mul_iso_hodge_pow_eight | exact GlobalTheory.HodgePow.hodge_eight_mul_iso_hodge_pow_eight | (intros; apply GlobalTheory.HodgePow.hodge_eight_mul_iso_hodge_pow_eight <;> assumption)
