import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComplexPointsOffOpenFinite
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BcDensEqOfGram
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CxPts GlobalTheory.VB
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.complex_points_off_open_finite : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) [IsIntegral X], IsArithVar p 1 → ∀ U : X.Opens, genericPoint X ∈ U → ∀ σ : k →+* ℂ, (ptsIn p σ U)ᶜ.Finite := by
  first | exact @GlobalTheory.SurfacePoints.finite_compl_ptsIn | exact GlobalTheory.SurfacePoints.finite_compl_ptsIn | (intros; apply GlobalTheory.SurfacePoints.finite_compl_ptsIn <;> assumption)
