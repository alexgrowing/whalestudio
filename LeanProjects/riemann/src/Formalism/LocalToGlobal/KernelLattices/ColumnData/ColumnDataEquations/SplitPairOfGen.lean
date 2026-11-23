import Formalism.LocalToGlobal.KernelLattices.ColumnData.ColumnDataEquations.SqLTop
import Formalism.LocalToGlobal.KernelLattices.ColumnData.BaseLinkOfNonzeroDelta
import Formalism.LocalToGlobal.KernelLattices.ColumnData.ProvisionExtensionLink
import Formalism.LocalToGlobal.PairingIndexBounds.SplitPairEquations.SplitPairGen
import Formalism.LocalRingCardinality.SpanPowerMembership.ExampleLayerExistsGenerators
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.SplitPairGen

noncomputable section
open NumberField Matrix

namespace Formalism.L2.Ker.Cd.PairingIndexBounds.Eq.SqG

open Formalism.L2.PairingIndexBounds.Eq.SqG

theorem splitPair_of_gen (h : SplitPairGen) (D : Formalism.L2.Ker.Car) : SquareSplitPairs.SplitPair D := by
  have hCM : IsCMField D.host.E := Formalism.HC.HostAx.isCMField_hostE D.host.toHostAx
  have hcj : ∀ y : D.host.E, D.host.conj y = star y := by
    intro y
    obtain ψ := Classical.choice (inferInstance : Nonempty (D.host.E →+* ℂ))
    apply ψ.injective
    rw [Formalism.HC.HostAx.conjE_apply D.host.toHostAx ψ y]
    exact (NumberField.IsCMField.complexEmbedding_complexConj D.host.E ψ y).symm
  have hU : PI.IsCMUnram D.host.E := by
    refine ⟨hCM.to_isTotallyComplex, fun φ a => ?_, fun P hP => ?_⟩
    · rw [← hcj]
      exact Formalism.HC.HostAx.conjE_apply D.host.toHostAx φ a
    · have hne : P ≠ ⊥ :=
        Ring.ne_bot_of_isMaximal_of_not_isField hP (NumberField.RingOfIntegers.not_isField _)
      have h2 := Formalism.HC.HostDer.unramEF D.host.der P hP.isPrime hne
      push_neg at h2
      obtain ⟨x, hx⟩ := h2
      refine ⟨x, D.host.conj • x, ?_, ?_⟩
      · exact hcj (x : D.host.E)
      · intro hm
        apply hx
        have h3 : D.host.conj • x - x = -(x - D.host.conj • x) := by ring
        rw [h3]
        exact P.neg_mem hm
  intro N' L' L'' hN hL' hL'' n hn
  exact h D.host.E hU N' L' L'' hN hL' hL'' n hn

theorem eqP_gen {D : Formalism.L2.Ker.Car} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} (B : Formalism.L2.Ker.Cd.Base D cc δ)
    (hcc : Formalism.L2.Ker.Cd.TaylorLogMetric.IsCurveIdeal D cc) (hδ : Formalism.L2.Ker.Cd.TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D cc δ) (hδ0 : δ ≠ 0) (hS : B.StdOK)
    (χ : Formalism.L2.Ker.Cd.TaylorLogMetric.IdE D → ℂ) (hχ : Formalism.L2.Ker.Cd.TaylorLogMetric.IsChi D χ) (hG : SplitPairGen) : B.EqP χ :=
  SquareSplitPairs.eqP_of_pair B hcc hδ hδ0 hS χ hχ (splitPair_of_gen hG D)

theorem delta_ne {D : Formalism.L2.Ker.Car} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ}
    (hcc : Formalism.L2.Ker.Cd.TaylorLogMetric.IsCurveIdeal D cc) (hδ : Formalism.L2.Ker.Cd.TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D cc δ) : δ ≠ 0 := Formalism.L2.Ker.Cd.IntegralLatticeDensity.delta_nonzero_link D cc hcc δ hδ

theorem eqP_all {D : Formalism.L2.Ker.Car} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ}
    (B : Formalism.L2.Ker.Cd.Base D cc δ) (hcc : Formalism.L2.Ker.Cd.TaylorLogMetric.IsCurveIdeal D cc) (hδ : Formalism.L2.Ker.Cd.TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D cc δ)
    (hS : B.StdOK) (χ : Formalism.L2.Ker.Cd.TaylorLogMetric.IdE D → ℂ) (hχ : Formalism.L2.Ker.Cd.TaylorLogMetric.IsChi D χ) (hP : SplitPairGen) : B.EqP χ :=
  eqP_gen B hcc hδ (delta_ne hcc hδ) hS χ hχ hP

theorem eqP_car {D : Formalism.L2.Ker.Car} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ}
    (B : Formalism.L2.Ker.Cd.Base D cc δ) (hcc : Formalism.L2.Ker.Cd.TaylorLogMetric.IsCurveIdeal D cc) (hδ : Formalism.L2.Ker.Cd.TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D cc δ)
    (χ : Formalism.L2.Ker.Cd.TaylorLogMetric.IdE D → ℂ) (hχ : Formalism.L2.Ker.Cd.TaylorLogMetric.IsChi D χ) : B.EqP χ :=
  eqP_all B hcc hδ (Formalism.L2.Ker.Cd.IntegralLatticeDensity.SO.stdOK B hcc hδ) χ hχ split_pair_generation

end Formalism.L2.Ker.Cd.PairingIndexBounds.Eq.SqG

end
