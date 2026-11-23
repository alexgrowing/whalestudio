import Formalism.LocalToGlobal.KernelLattices.FirstKernelLawReading

noncomputable section

namespace Formalism.L2.KerInert

open NumberField Formalism.BasicNotions Formalism.L2.Ker

def AlgTAll : Prop :=
  ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Base D cc δ) (χ : Formalism.MainNotions.TaylorLogMetric.IdE D → ℂ),
    Formalism.MainNotions.TaylorLogMetric.IsCurveIdeal D cc → Formalism.MainNotions.TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D cc δ → Formalism.MainNotions.TaylorLogMetric.IsChi D χ → B.AlgT χ

end Formalism.L2.KerInert
