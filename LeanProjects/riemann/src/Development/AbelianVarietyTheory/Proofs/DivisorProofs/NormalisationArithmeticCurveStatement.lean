import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormalisationArithmeticCurve
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMemChart
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CxPts GlobalTheory.VB
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.normalisation_arithmetic_curve : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) [IsIntegral X], IsArithVar p 1 → ∃ (Y : Scheme.{0}) (_ : IsIntegral Y) (ν : Y ⟶ X), IsFinite ν ∧ ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme Y ∧ IsArithVar (ν ≫ p) 1 ∧ ν (genericPoint Y) = genericPoint X ∧ ν.residueDegree (genericPoint Y) ≠ 0 := by
  first | exact @GlobalTheory.NormalCover.exists_normal_surface | exact GlobalTheory.NormalCover.exists_normal_surface | (intros; apply GlobalTheory.NormalCover.exists_normal_surface <;> assumption)
