import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAbelianSchemeBaseChangeFieldAndComm
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isAbelianScheme_and_comm_baseChange_field : ∀ (K L : Type) [Field K] [Field L] [Algebra K L] (A : Over (Sp K)) [GrpObj A] [IsCommMonObj A], IsAbelianScheme A → IsAbelianScheme ((Over.pullback (spMap (algebraMap K L))).obj A) ∧ IsCommMonObj ((Over.pullback (spMap (algebraMap K L))).obj A) := by
  first | exact @GlobalTheory.Published.AbVarRed.isAbelianScheme_baseChange_field_and_comm | exact GlobalTheory.Published.AbVarRed.isAbelianScheme_baseChange_field_and_comm | (intros; apply GlobalTheory.Published.AbVarRed.isAbelianScheme_baseChange_field_and_comm <;> assumption)
