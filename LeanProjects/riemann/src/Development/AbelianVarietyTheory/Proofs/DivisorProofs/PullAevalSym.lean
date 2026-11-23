import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsMetricFrOfIsMetricOn
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ChernDegreeComplex
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc
open scoped Matrix ContDiff ComplexOrder

set_option autoImplicit false

namespace GlobalTheory.ChernCalc

theorem pull_aeval_sym : ∀ (n n' : ℕ) (L : V n' →L[ℂ] V n) (P : MvPolynomial (Fin n × Fin n) ℂ), pull L ((aeval sym P : Ev n) : Alt n) = ((aeval sym (aeval (fun x : Fin n × Fin n => ∑ c, ∑ d, C (L (coordVec c) x.1 * (starRingEnd ℂ) (L (coordVec d) x.2)) * (X (c, d) : MvPolynomial (Fin n' × Fin n') ℂ)) P) : Ev n') : Alt n') := by
  intro n n' L P
  rw [MvPolynomial.comp_aeval_apply]
  have key : (pull L).comp ((Subalgebra.center ℂ (Alt n)).val.comp (aeval sym)) = (Subalgebra.center ℂ (Alt n')).val.comp
      (aeval fun x : Fin n × Fin n => aeval sym (∑ c, ∑ d,
        C (L (coordVec c) x.1 * (starRingEnd ℂ) (L (coordVec d) x.2)) * (X (c, d) : MvPolynomial (Fin n' × Fin n') ℂ))) := by
    refine MvPolynomial.algHom_ext fun x => ?_
    simp only [AlgHom.comp_apply, aeval_X, map_sum, map_mul, aeval_C, Subalgebra.coe_val, sym, (pull_dz L _).1,
      (pull_dz L _).2, Finset.sum_mul_sum, AlgHom.commutes, smul_mul_smul_comm]
    refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => ?_
    simp only [Algebra.smul_def, map_mul]
  exact congrArg (fun f => f P) key

end GlobalTheory.ChernCalc
