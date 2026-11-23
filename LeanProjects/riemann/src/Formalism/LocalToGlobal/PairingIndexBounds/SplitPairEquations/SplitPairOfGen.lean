import Formalism.LocalToGlobal.PairingIndexBounds.SplitPairEquations.SquareSplitPairs.EqPOfPair
import Formalism.LocalToGlobal.PairingIndexBounds.SplitPairEquations.SplitPairGen

noncomputable section
open NumberField Matrix

namespace Formalism.L2.PairingIndexBounds.Eq.SqG

theorem splitPair_of_gen (h : SplitPairGen) (D : Formalism.BasicNotions.D7) : SquareSplitPairs.SplitPair D := by
  letI := D.host.cmStar
  intro N' L' L'' hN h1 h2 n hn
  exact h D.host.E D.sp.cm.cmUnram N' L' L'' hN h1 h2 n hn

theorem eqP_gen {D : Formalism.BasicNotions.D7} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} (B : Formalism.L2.Ker.Base D cc δ)
    (hcc : Formalism.MainNotions.TaylorLogMetric.IsCurveIdeal D cc) (hδ : Formalism.MainNotions.TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D cc δ) (hδ0 : δ ≠ 0) (hS : B.StdOK)
    (χ : Formalism.MainNotions.TaylorLogMetric.IdE D → ℂ) (hχ : Formalism.MainNotions.TaylorLogMetric.IsChi D χ) (hG : SplitPairGen) : B.EqP χ :=
  SquareSplitPairs.eqP_of_pair B hcc hδ hδ0 hS χ hχ (splitPair_of_gen hG D)

end Formalism.L2.PairingIndexBounds.Eq.SqG
