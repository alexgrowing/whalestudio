import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DetNeZeroOfRealIndependentIsotropicHermitian
import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsLatBasisZero
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SpanPeriodLatticeComplexSemiAbelianEqTopStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor GlobalTheory.ShFam.Hor.LogCh
open scoped Matrix CategoryTheory.Obj Topology
attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.det_ne_zero_of_real_independent_isotropic_hermitian : ∀ (g : ℕ) (Hm : Matrix (Fin g) (Fin g) ℂ) (E : Fin g → Fin g → ℂ), (∀ z : Fin g → ℂ, z ≠ 0 → 0 < (hermForm Hm z z).re) → LinearIndependent ℝ E → (∀ i j, (hermForm Hm (E i) (E j)).im = 0) → (Matrix.of fun k i => E i k).det ≠ 0 := by
  first | exact @GlobalTheory.det_ne_zero_of_real_indep_isotropic | exact GlobalTheory.det_ne_zero_of_real_indep_isotropic | (intros; apply GlobalTheory.det_ne_zero_of_real_indep_isotropic <;> assumption)
