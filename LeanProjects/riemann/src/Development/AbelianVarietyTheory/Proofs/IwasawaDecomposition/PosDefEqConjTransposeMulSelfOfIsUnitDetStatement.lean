import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PosDefEqConjTransposeMulSelfOfIsUnitDet
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MultOfNotMem
open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame
open GlobalTheory.PointChern Filter Topology
open scoped Matrix
open scoped ComplexOrder

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_isUnit_det_conjTranspose_mul_eq_of_posDef : ∀ {p : ℕ} (P : Matrix (Fin p) (Fin p) ℂ), P.PosDef → ∃ A : Matrix (Fin p) (Fin p) ℂ, IsUnit A.det ∧ Aᴴ * A = P := by
  first | exact @GlobalTheory.posDef_eq_conjTranspose_mul_self_of_isUnit_det | exact GlobalTheory.posDef_eq_conjTranspose_mul_self_of_isUnit_det | (intros; apply GlobalTheory.posDef_eq_conjTranspose_mul_self_of_isUnit_det <;> assumption)
