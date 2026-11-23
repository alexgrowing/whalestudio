import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.ScaledExample
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo NumberField

noncomputable section

def DualMetricEnergy.Statement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (i : ℕ) (F : HermLattice K i) (T : Type) [Fintype T]
    [DecidableEq T] (b : Module.Basis T ℤ (dualLattice F))
    (hb : Function.Bijective (Matrix.mulVecLin (dualEmbMatrix b))), 1 ≤ i →
    ∑ k ∈ Finset.range i,
        ptsIntegral (dualIdeal b)
          (pot fun j : Fin (i - 1) =>
            if (j : ℕ) < k then dualLine F b hb else dualLine F.withStdMetric b hb)
          (fun z => Real.log ((dualLine F b hb).h z) - Real.log ((dualLine F.withStdMetric b hb).h z)) =
      1 / 2 * (∑ σ : K →+* ℂ, Real.log (F.metric σ).det.re) *
        geomDeg (grassIdeal 1 1 (i - 1)) (fsMulti (plBlocks 1 1 (i - 1))) (1 * 1 * (i - 1))

example : Σ' (b : Module.Basis Unit ℤ (dualLattice HermLattice.scaledExample)),
    Function.Bijective (Matrix.mulVecLin (dualEmbMatrix b)) ∧ 1 ≤ 1 ∧
      HermLattice.scaledExample.metric ≠ HermLattice.scaledExample.withStdMetric.metric :=
  ⟨dualBasisStandard, dualEmbMatrix_standard_bijective, le_rfl, fun h => by
    have h1 := congrFun (congrFun (congrFun h (Rat.castHom ℂ)) 0) 0
    simp [HermLattice.scaledExample, HermLattice.withStdMetric] at h1⟩

end

end GroundTheory.Heights₂.Heights
