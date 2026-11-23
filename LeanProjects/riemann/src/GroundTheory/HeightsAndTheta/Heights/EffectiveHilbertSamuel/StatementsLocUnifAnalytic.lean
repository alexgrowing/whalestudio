import Mathlib
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.EffectiveHS

open Set Filter Topology

def LocUnifAnalytic.Statement : Prop :=
  ∀ (D : ℕ) (V : Set (Fin D → ℂ)) (f : ℕ → (Fin D → ℂ) → ℂ) (g : (Fin D → ℂ) → ℂ),
    IsOpen V → (∀ n, AnalyticOnNhd ℂ (f n) V) → TendstoLocallyUniformlyOn f g atTop V →
      AnalyticOnNhd ℂ g V
