import Mathlib
import Formalism.LocalToGlobal.GlobalTheory.GL3.PHfInt
import Formalism.LocalToGlobal.GlobalTheory.GL3.PSelfDual

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity

open NumberField Formalism.BasicNotions Formalism.MainNotions.TaylorLogMetric

theorem hermitian_form_integral_values : HfIntRec := HfIntRec_of_gen (HfGenRec_of_arith arithmetic_hermitian_form)

theorem theta_operator_isometry : ∀ D : D7, ∀ cc : Ideal (𝓞 D.host.K), IsCurveIdeal D cc → ∀ δ : ℂ,
    IsDiscriminantTwelfthRootOfIdealLattice D cc δ → IopIso D (tor0 D cc δ) :=
  IopIso_of_parts hermitian_form_integral_values self_dual_lattice

theorem theta_norm_indep_of_pair : LinkThIndep := LinkThIndep_of_arith' arithmetic_hermitian_form

end Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity

end
