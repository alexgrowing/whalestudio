import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsNormalMvPolynomialOfIsNormal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverCompOfIsClosedImmersion
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Geo.Tor
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isNormal_mvPolynomial_of_isNormal : ∀ (R : Type) [CommRing R] (r : ℕ), ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme (Sp R) → ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme (Sp (MvPolynomial (Fin r) R)) := by
  first | exact @GlobalTheory.isNormalScheme_sp_mvPolynomial | exact GlobalTheory.isNormalScheme_sp_mvPolynomial | (intros; apply GlobalTheory.isNormalScheme_sp_mvPolynomial <;> assumption)
