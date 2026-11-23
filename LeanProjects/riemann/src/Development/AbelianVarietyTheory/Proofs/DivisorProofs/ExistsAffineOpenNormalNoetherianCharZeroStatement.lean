import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAffineOpenNormalNoetherianCharZero
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SymTupOne
import Development.AbelianVarietyTheory.Statements.TorsionEndomorphisms.EndDeterminedOnTorsion
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.MinSt2
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GlueProjectiveSpaceMapsOfAgreeGeometricPointsStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_affineOpen_normal_noetherian_charZero : ∀ (X : Scheme.{0}), Geo.Tor.IsNormalScheme X → IsLocallyNoetherian X → (∀ x : X, CharZero (X.residueField x)) → ∀ x : X,
    ∃ U : X.affineOpens, x ∈ (U : X.Opens) ∧ IsDomain Γ(X, U) ∧ IsNoetherianRing Γ(X, U) ∧ IsIntegrallyClosed Γ(X, U) ∧ CharZero Γ(X, U) := by
  first | exact @GlobalTheory.exists_affineOpen_isIntegrallyClosed_charZero | exact GlobalTheory.exists_affineOpen_isIntegrallyClosed_charZero | (intros; apply GlobalTheory.exists_affineOpen_isIntegrallyClosed_charZero <;> assumption)
