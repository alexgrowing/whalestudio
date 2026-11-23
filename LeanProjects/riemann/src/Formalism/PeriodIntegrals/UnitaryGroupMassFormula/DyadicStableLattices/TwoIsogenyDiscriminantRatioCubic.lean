import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.DyadicStableLattices.DeuringScale

noncomputable section
open Filter Topology
open scoped ComplexConjugate

namespace PI.GoodTwo
namespace IsogenyReduction

lemma alg (e g2 g3 : ℂ) (h : g3 = 4 * e ^ 3 - g2 * e) (hd : g2 ^ 3 - 27 * g3 ^ 2 ≠ 0) :
    ((60 * e ^ 2 - 4 * g2) ^ 3 - 27 * (g3 + 84 * e ^ 3 - 7 * g2 * e) ^ 2
      + 16 * (g2 ^ 3 - 27 * g3 ^ 2)) ^ 3 =
    1728 * g2 ^ 3 / (g2 ^ 3 - 27 * g3 ^ 2) *
      ((60 * e ^ 2 - 4 * g2) ^ 3 - 27 * (g3 + 84 * e ^ 3 - 7 * g2 * e) ^ 2) *
      (g2 ^ 3 - 27 * g3 ^ 2) ^ 2 := by
  rw [div_mul_eq_mul_div, div_mul_eq_mul_div, eq_div_iff hd]
  subst h
  ring

end IsogenyReduction

open IsogenyReduction

end PI.GoodTwo
