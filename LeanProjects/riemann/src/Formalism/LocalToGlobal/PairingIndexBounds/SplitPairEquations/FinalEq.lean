import Formalism.LocalToGlobal.PairingIndexBounds.SplitPairEquations.Outright
import Formalism.LocalToGlobal.GlobalTheory.GL3.PStdOK

namespace Formalism.L2.PairingIndexBounds.Eq.SqG

theorem eulerProduct_eq_of_curve_ideal {D : Formalism.BasicNotions.D7} {cc : Ideal (NumberField.RingOfIntegers D.host.K)} {δ : ℂ}
    (B : Formalism.L2.Ker.Base D cc δ) (hcc : Formalism.MainNotions.TaylorLogMetric.IsCurveIdeal D cc) (hδ : Formalism.MainNotions.TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D cc δ)
    (χ : Formalism.MainNotions.TaylorLogMetric.IdE D → ℂ) (hχ : Formalism.MainNotions.TaylorLogMetric.IsChi D χ) : B.EqP χ :=
  eqP_outright B hcc hδ (Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.SO.stdOK B hcc hδ) χ hχ

end Formalism.L2.PairingIndexBounds.Eq.SqG
