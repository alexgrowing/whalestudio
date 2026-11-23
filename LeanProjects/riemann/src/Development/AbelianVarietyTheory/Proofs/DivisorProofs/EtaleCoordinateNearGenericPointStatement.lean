import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleCoordinateNearGenericPoint
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BcDensEqOfGram
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CxPts GlobalTheory.VB
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.etale_coordinate_near_generic_point : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) [IsIntegral X], IsArithVar p 1 → ∃ (U : X.Opens) (x : Fin 1 → Γ(X, U)), IsAffineOpen U ∧ genericPoint X ∈ U ∧ (MvPolynomial.eval₂Hom (algX p U) x).Etale := by
  first | exact @GlobalTheory.GenericEtale.exists_etale_coord_surface | exact GlobalTheory.GenericEtale.exists_etale_coord_surface | (intros; apply GlobalTheory.GenericEtale.exists_etale_coord_surface <;> assumption)
