import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemiAbelianDirectFactorOfIdempotent
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.MinSt2
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.semiAbelian_direct_factor_of_idempotent : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ e : G ⟶ G, IsMonHom e → e ≫ e = e → ∃ (H : Over S) (_ : GrpObj H) (i : H ⟶ G) (r : G ⟶ H), IsMonHom i ∧ IsMonHom r ∧ i ≫ r = 𝟙 H ∧ r ≫ i = e ∧ IsSemiAbelian H := by
  first | exact @GlobalTheory.SiegMin.exists_semiAbelian_idempotent_image | exact GlobalTheory.SiegMin.exists_semiAbelian_idempotent_image | (intros; apply GlobalTheory.SiegMin.exists_semiAbelian_idempotent_image <;> assumption)
