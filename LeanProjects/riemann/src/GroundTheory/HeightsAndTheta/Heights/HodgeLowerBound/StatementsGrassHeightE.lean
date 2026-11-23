import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsGrassHeight
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.AssemblyAnalytic
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open ReciprocityTheory.ChartRestriction.G.Geo GroundTheory.Heights₂.Heights Matrix

noncomputable section

def UnitDetBound (m j : ℕ) (e : ℝ) : Prop :=
  ∀ Z : Matrix (Fin m) (Fin j) ℂ, (∀ a b, ‖Z a b‖ = 1) → 1 / 2 * Real.log (1 + Z * Zᴴ).det.re ≤ e

def RootLogNormBoundE.Statement : Prop :=
  ∀ (f j m : ℕ) (e : ℝ) (ζ : Fin f → Matrix (Fin j) (Fin m) ℂ), UnitDetBound m j e → IsRootMatrix ζ →
    ∀ z ∈ mcPts (rootPointIdeal ζ),
      -((f : ℝ) * e) ≤ logNorm (fsMulti (plBlocks f j m)) (rootAnchorSection f j m) z

def RootHeightE.Statement : Prop :=
  ∀ (f j m : ℕ) (e : ℝ) (ζ : Fin f → Matrix (Fin j) (Fin m) ℂ), 1 ≤ f → UnitDetBound m j e → IsRootMatrix ζ →
    ∀ II : IntersectionSystem, IsIntersectionSystem II →
      II (Fin f) (plBlocks f j m) (rootPointIdeal ζ) 1 ![fsMulti (plBlocks f j m)] ≤
        (f : ℝ) * e * degC (rootPointIdeal ζ)

def GrassHeightE.Statement : Prop :=
  SuccessiveMinimaUpperBound → ∀ (f j m : ℕ) (e : ℝ), 1 ≤ f → UnitDetBound m j e →
    ∀ II : IntersectionSystem, IsIntersectionSystem II →
      II (Fin f) (plBlocks f j m) (grassIdeal f j m) (f * j * m + 1) (fun _ => fsMulti (plBlocks f j m)) ≤
        ((f * j * m + 1 : ℕ) : ℝ) * ((f : ℝ) * e) *
          geomDeg (grassIdeal f j m) (fsMulti (plBlocks f j m)) (f * j * m)

end

end GroundTheory.Heights₂.Heights.LowerBoundFree
