import ReciprocityTheory.L2DbarEstimates.JacobianInterpolationStatement
import ReciprocityTheory.L2DbarEstimates.NormFibrations.Imports
import ReciprocityTheory.L2DbarEstimates.ChartDerivatives.InhHasFDerivAtNormSq
import ReciprocityTheory.L2DbarEstimates.Mollifiers.Imports
import ReciprocityTheory.L2DbarEstimates.WeakHolomorphy.Imports
import ReciprocityTheory.L2DbarEstimates.WeakHolomorphy.RegBall
import ReciprocityTheory.L2DbarEstimates.MinimalSolutions.HilbertLemmas
import ReciprocityTheory.L2DbarEstimates.BasicIdentity.ImportsAlt
import ReciprocityTheory.L2DbarEstimates.HormanderEstimate.HStatementOf
import ReciprocityTheory.L2DbarEstimates.HormanderEstimate.Closed
import ReciprocityTheory.L2DbarEstimates.SkodaWeights.Imports
import ReciprocityTheory.L2DbarEstimates.LeviForms.Imports

universe u

namespace ReciprocityTheory.L2DbarEstimates

open MeasureTheory

theorem regMAll (n : ℕ) (M : Type*) [TopologicalSpace M] [T2Space M]
    [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M] : F.RegMStatement n M :=
  F.regM n M C.reg (F.extend n M)

theorem hormander (n : ℕ) (M : Type*) [TopologicalSpace M] [T2Space M]
    [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M] : HStatement n M :=
  F.hStatement_of n M (E.ap n M) (E.tStarIbp n M) (chain n M) C.reg
    (B.moll_graph (V n) volume ℝ) (B.moll_smooth (V n) volume) (B.moll_support (V n) volume)
    (B.kernel_std (V n) volume)

theorem skoda (n : ℕ) (M : Type*) [TopologicalSpace M] [T2Space M]
    [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M] : SStatement n M :=
  H.skoda n M (fun p => hormander n (M × Fin p))
    (fun p => F.needBergmanClosed n (M × Fin p) (regMAll n (M × Fin p)))

theorem tw (n : ℕ) (M : Type u) [TopologicalSpace M] [T2Space M]
    [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M] : TWStatement n M :=
  I.tw n M (hormander n M) (F.holoClosedNeed n M (regMAll n M))

theorem ot0 (n : ℕ) (M : Type u) [TopologicalSpace M] [T2Space M]
    [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M] : JacobianInterpolationStatement n M := by
  have hB := I.basic n M
  have hTL : I.TwistLeviStatement n M :=
    I.twistLevi n M (I.logLevi n M (I.evLevi n M) (chain n M)) (chain n M) hB
  have hA : I.ApplyStatement n M := I.applyTw n M (tw n M) hTL (I.dual n M hTL hB) hB
  have hF : I.FixedStatement n M :=
    I.fixed n M hA hB (I.vanish n C.mv C.mvDiv) (F.holoClosedNeed n M (regMAll n M))
      (F.evalNeed n M C.mv) (fun H _ _ _ => cvx H)
  exact I.ot0 n M hF (I.shellBound n M (I.polar n) (I.cov n)) (I.localData n M) I.cutoff

theorem ma (n : ℕ) : MAStatement n :=
  I.ma n (I.maCof n)

theorem detMono (n : ℕ) : DetMonoStatement n :=
  I.maDet n

theorem inhabited (n : ℕ) : InhabitedStatement n :=
  etaleStein_nonempty n

end ReciprocityTheory.L2DbarEstimates
