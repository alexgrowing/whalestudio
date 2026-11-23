import Formalism.LocalToGlobal.PairingIndexBounds.SplitPairEquations.EqPAll
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.SplitPairGen

namespace Formalism.L2.PairingIndexBounds.Eq.SqG

theorem eqP_outright {D : Formalism.BasicNotions.D7} {cc : Ideal (NumberField.RingOfIntegers D.host.K)} {δ : ℂ}
    (B : Formalism.L2.Ker.Base D cc δ) (hcc : Formalism.MainNotions.TaylorLogMetric.IsCurveIdeal D cc) (hδ : Formalism.MainNotions.TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D cc δ)
    (hS : B.StdOK) (χ : Formalism.MainNotions.TaylorLogMetric.IdE D → ℂ) (hχ : Formalism.MainNotions.TaylorLogMetric.IsChi D χ) : B.EqP χ :=
  eqP_all B hcc hδ hS χ hχ split_pair_generation

end Formalism.L2.PairingIndexBounds.Eq.SqG
