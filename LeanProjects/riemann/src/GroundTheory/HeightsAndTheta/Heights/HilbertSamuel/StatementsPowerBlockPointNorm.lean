import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsPowerBlockMeasure
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry MeasureTheory

noncomputable section

def PowerBlockPointNorm.Statement : Prop :=
  ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    (y : (Σ k, ι k) → Ω) (A : HermLine ι) (m N : ℕ) (v : Fin N → Ω) (B : HermLine (addIdx ι N)),
    ContinuousOn A.h {z | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0} → B.a = unitDeg (none : Option K) →
    (∀ j, v j ∈ chartLat y A.a m) →
    (∀ z ∈ mcPts (mCoordIdeal (addBlock y v)), ∀ j : Fin N,
      secNormAt y A m (v j) (basePart₂ z) * B.h z = ‖z ⟨none, j⟩‖) →
    ∀ (q : ℕ) (F : MRing (addIdx ι N)), IsMultiHomog F (blockDeg (none : Option K) q) →
      ContinuousOn (secNormAt y A (m * q) (aeval (addBlock y v) F)) (mcPts (mCoordIdeal y)) ∧
      ∀ z ∈ mcPts (mCoordIdeal (addBlock y v)),
        secNormAt y A (m * q) (aeval (addBlock y v) F) (basePart₂ z) =
          ‖eval z (map (Int.castRingHom ℂ) F)‖ / B.h z ^ q

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
