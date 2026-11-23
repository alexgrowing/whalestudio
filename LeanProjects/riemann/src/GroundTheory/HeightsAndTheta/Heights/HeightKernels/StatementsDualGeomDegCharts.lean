import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsChartMass
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.ScaledExample
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo NumberField Matrix
open scoped ComplexOrder

noncomputable section

def DualGeomDegCharts.Statement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (i : ℕ) (F : HermLattice K i) (T : Type) [Fintype T]
    [DecidableEq T] (b : Module.Basis T ℤ (dualLattice F))
    (hb : Function.Bijective (Matrix.mulVecLin (dualEmbMatrix b))), 1 ≤ i →
    ∃ A : (K →+* ℂ) → Matrix (Fin i) (Fin (i - 1 + 1)) ℂ, (∀ σ, Function.Bijective (A σ).mulVec) ∧
      geomDeg (dualIdeal b) (dualLine F b hb) (i - 1) =
        ∑ σ : K →+* ℂ, chartMass ((A σ)ᴴ * F.metric σ * A σ)

example : Σ' (b : Module.Basis Unit ℤ (dualLattice HermLattice.scaledExample)),
    Function.Bijective (Matrix.mulVecLin (dualEmbMatrix b)) ∧ 1 ≤ 1 :=
  ⟨dualBasisStandard, dualEmbMatrix_standard_bijective, le_rfl⟩

example : Function.Bijective (1 : Matrix (Fin 1) (Fin (1 - 1 + 1)) ℂ).mulVec := by
  have h : (1 : Matrix (Fin 1) (Fin 1) ℂ).mulVec = id := funext Matrix.one_mulVec
  exact h ▸ Function.bijective_id

end

end GroundTheory.Heights₂.Heights
