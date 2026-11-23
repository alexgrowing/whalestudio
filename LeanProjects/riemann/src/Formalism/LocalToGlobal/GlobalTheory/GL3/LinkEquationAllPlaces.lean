import Mathlib
import Formalism.LocalToGlobal.GlobalTheory.GL3.PFamily
import Formalism.LocalToGlobal.GlobalTheory.GL3.ProvisionExtensionLink
import Formalism.LocalToGlobal.PairingIndexBounds.SplitPairEquations.EqPAll
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.SplitPairGen

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.RestB

open NumberField Formalism.BasicNotions Formalism.MainNotions.TaylorLogMetric Formalism.L2.Ker Classical

def LinkEqPAll : Prop :=
  ∀ D : D7, ∀ cc : Ideal (𝓞 D.host.K), IsCurveIdeal D cc → ∀ δ : ℂ, IsDiscriminantTwelfthRootOfIdealLattice D cc δ →
    ∀ B : Base D cc δ, ∀ χ : IdE D → ℂ, IsChi D χ → B.EqP χ

end Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.RestB

end
