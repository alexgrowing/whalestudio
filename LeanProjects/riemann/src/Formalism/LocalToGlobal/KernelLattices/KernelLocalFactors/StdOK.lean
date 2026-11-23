import Formalism.LocalToGlobal.GlobalTheory.GL3.PStdOK

open NumberField Formalism.BasicNotions Formalism.MainNotions

namespace Formalism.L2.Ker

theorem Base.stdOK {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} (B : Base D cc δ) (hcc : TaylorLogMetric.IsCurveIdeal D cc)
    (hδ : TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D cc δ) : B.StdOK :=
  Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.SO.stdOK B hcc hδ

end Formalism.L2.Ker
