import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GeometricallyConnectedSmoothProjModificationOffO
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsoOverOfIsOpenImmersion
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompHS
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.geometricallyConnected_smoothProjModification_offOpen : ∀ (F : Type) [Field F] (X : Scheme.{0}) [IsIntegral X] (sX : X ⟶ Sp F) (n : ℕ) [SmoothOfRelativeDimension n sX] (U : X.Opens) (M : Modif sX U n) [IsIntegral M.X] [GeometricallyConnected sX], (U : Set X).Nonempty → GeometricallyConnected M.str := by
  first | exact @GlobalTheory.ModifGeomConn.geometricallyConnected_modif | exact GlobalTheory.ModifGeomConn.geometricallyConnected_modif | (intros; apply GlobalTheory.ModifGeomConn.geometricallyConnected_modif <;> assumption)
