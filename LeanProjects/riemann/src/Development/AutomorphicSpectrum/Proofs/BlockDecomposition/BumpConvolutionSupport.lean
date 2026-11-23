import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.WaveSt
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsMultOfFintype

noncomputable section

open MeasureTheory Matrix Finset
open scoped ContDiff ComplexConjugate InnerProductSpace

open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC
open GlobalTheory.CompanionTheory.WaveMult

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace GlobalTheory.CompanionTheory.WaveMult

theorem hasCompactSupport_of_isBump {g : ℝ → ℝ} {T : ℝ} (hg : IsBump g T) : HasCompactSupport g := by
  refine HasCompactSupport.intro (isCompact_closedBall (0 : ℝ) T) fun x hx => hg.2.2 x ?_
  rw [Metric.mem_closedBall, Real.dist_eq, sub_zero, not_le] at hx
  exact hx

theorem isBump_gconv : ∀ (g g' : ℝ → ℝ) (T T' : ℝ), IsBump g T → IsBump g' T' → IsBump (gconv g g') (T + T') := by
  intro g g' T T' hg hg'
  refine ⟨?_, ?_, ?_⟩
  · have hconv : gconv g g' = MeasureTheory.convolution g g' (ContinuousLinearMap.mul ℝ ℝ) volume := by
      funext r
      simp [gconv, MeasureTheory.convolution]
    rw [hconv]
    exact (hasCompactSupport_of_isBump hg').contDiff_convolution_right (ContinuousLinearMap.mul ℝ ℝ)
      hg.1.continuous.locallyIntegrable hg'.1
  · intro r
    unfold gconv
    calc ∫ t, g t * g' (-r - t) = ∫ t, g (-t) * g' (-r - -t) := (integral_neg_eq_self _ _).symm
      _ = ∫ t, g t * g' (r - t) := by
        congr 1
        funext t
        rw [hg.2.1 t, show -r - -t = -(r - t) by ring, hg'.2.1]
  · intro r hr
    have hzero : ∀ t, g t * g' (r - t) = 0 := by
      intro t
      by_cases ht : T < |t|
      · rw [hg.2.2 t ht, zero_mul]
      · rw [hg'.2.2 (r - t) ?_, mul_zero]
        have h1 := abs_sub_abs_le_abs_sub r t
        have ht' := not_lt.mp ht
        linarith
    simp [gconv, hzero]

end GlobalTheory.CompanionTheory.WaveMult
