import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.IsGraphGenTwistBundleZero
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (chartRingOver secOver mIdealOver)

def StepEq.Statement : Prop :=
  ∀ (k : Type) [Field k] (N : ℕ) (Ω : Type) [Field Ω] [Algebra k Ω] (x : Fin (N + 1) → Ω)
    (Q : Kleiman.LineBundle k x) (n : ℤ) (m : ℕ) (s : Fin m → Ω), IsGraphGen Q n s →
    ∀ (d : ℕ) (r : ℚ) (a : ℕ) (mm : ℤ) (c₁ : ℕ) (σ : Ω),
      (∃ T : Kleiman.StepData k x, T.M = Q ∧ T.d + 1 = d ∧ T.t - T.s' = r ∧ T.p = a ∧ T.m = mm ∧
          T.c₁ = c₁ ∧ T.si = σ) ↔
        (1 ≤ d ∧ IndefiniteRowSideFullHecke.Kleiman2.IsStepData k (graphVec x s) baseBlock d (graphDeg n) r a mm c₁ σ)

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
