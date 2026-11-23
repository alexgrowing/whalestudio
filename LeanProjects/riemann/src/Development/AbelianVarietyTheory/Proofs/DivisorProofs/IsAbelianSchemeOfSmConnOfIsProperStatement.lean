import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAbelianSchemeOfSmConnOfIsProper
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified
import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isAbelianScheme_of_smConn_of_isProper' : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G], GlobalTheory.SS.SmConn G → IsProper G.hom → IsAbelianScheme G := by
  first | exact @GlobalTheory.SmConnProper.isAbelianScheme_of_smConn_of_isProper | exact GlobalTheory.SmConnProper.isAbelianScheme_of_smConn_of_isProper | (intros; apply GlobalTheory.SmConnProper.isAbelianScheme_of_smConn_of_isProper <;> assumption)
