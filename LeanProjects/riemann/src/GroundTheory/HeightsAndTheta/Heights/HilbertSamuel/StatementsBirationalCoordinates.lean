import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.ArithModel
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

def BirationalCoordinates.Statement : Prop :=
  ∀ (Ω : Type) [Field Ω] [CharZero Ω] (κ : Type) [Fintype κ] (x : Ix κ → Ω) (c : κ), x ⟨(), c⟩ ≠ 0 →
    ∃ (Ω' : Type) (_ : Field Ω') (_ : CharZero Ω') (x' : Ix κ → Ω'),
      mCoordIdeal (ι := GlobalTheory κ) x' = mCoordIdeal (ι := GlobalTheory κ) x ∧ Birational (ι := GlobalTheory κ) x' ∧
      ∀ (A : HermLine (GlobalTheory κ)) (τ : ℕ),
        smallSectionCount (IsSmallH (mCoordIdeal (ι := GlobalTheory κ) x') x' A) (chartLat (ι := GlobalTheory κ) x' A.a) τ =
          smallSectionCount (IsSmallH (mCoordIdeal (ι := GlobalTheory κ) x) x A) (chartLat (ι := GlobalTheory κ) x A.a) τ

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
