import Mathlib
import Formalism.SharpRestriction.GlobalSchurBounds.TaylorLogMetric
import Formalism.LocalToGlobal.GlobalTheory.GL3.Statement
import Formalism.LocalToGlobal.GlobalTheory.GL3.CubicFields.EpsteinZeta.AreaLatIOfDiscr
import Formalism.LocalToGlobal.GlobalTheory.GL3.CubicFields.EisensteinSeries.DslopePhiCDifferentiableAt
import Formalism.LocalToGlobal.GlobalTheory.GL3.CubicFields.EisensteinSeries.RemLipTermB
import Formalism.LocalToGlobal.GlobalTheory.GL3.CubicFields.DifferentIdeal.CoeIdealDifferentNeZero
import Formalism.LocalToGlobal.GlobalTheory.GL3.CubicFields.DifferentIdeal.AbsNormInvMulDifferent

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5

open NumberField Classical
open scoped Pointwise
open Formalism.BasicNotions (D7)
open Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity (IsLat jL Uniformization CMTransitive LinkPer KroneckerLimit DedekindFactor)
open Formalism.MainNotions.TaylorLogMetric (lamConj lamOf embT meanLogOm DataIn tor0 IsCurveIdeal IsDiscriminantTwelfthRootOfIdealLattice per22 logOmVal)

theorem br_area_eq (Λ : AddSubgroup ℂ) : Formalism.MainNotions.TaylorLogMetric.area Λ = area Λ := rfl

theorem br_jL_eq (Λ : AddSubgroup ℂ) : jL Λ = 1728 * g2 Λ ^ 3 / discr Λ := rfl

def brPhi (D : D7) : D.host.K →+* ℂ := D.host.φ₀.comp (algebraMap D.host.K D.host.E)

theorem br_lamOf_eq (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) :
    lamOf D cc δ = latI (brPhi D) cc δ := rfl

instance br_factPrime (D : D7) : Fact D.host.d.Prime := ⟨D.host.hyp.2.1⟩

end Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5

end
