import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StNormalModelDisc
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StNormalCurveRegularPoint
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

theorem NormalModelDisc.proof (hreg : NormalCurveRegularPoint.Statement) : NormalModelDisc.Statement := by
  intro n J M w _ hdim hw
  have hdim' : ringKrullDim (MvPolynomial (Fin n ⊕ Fin M.m) ℂ ⧸ M.ideal) = (1 : ℕ) := by
    rw [M.ringKrullDim_eq, hdim]
  obtain ⟨A, O, V, g, hO, -, hwV, hg, hAg, hZV⟩ :=
    hreg (Fin n ⊕ Fin M.m) M.ideal w M.isPrime M.isIntegrallyClosed hdim' hw
  have hwg : w ∈ g '' O := hZV ▸ ⟨hw, hwV⟩
  obtain ⟨y₀, hy₀, hgy₀⟩ := hwg
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hO y₀ hy₀
  have hmem : ∀ τ ∈ Metric.ball (0 : Fin 1 → ℂ) r, y₀ + τ ∈ O := fun τ hτ ↦ hball (by
    rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left]
    simpa using hτ)
  refine ⟨r, hr, fun τ ↦ g (y₀ + τ), ?_, ?_, ?_, ?_⟩
  · intro τ hτ
    exact ((hg _ (hmem τ hτ)).differentiableAt.comp τ
      (differentiableAt_const y₀ |>.add differentiableAt_id)).differentiableWithinAt
  · intro s hs t ht hst
    have h := congrArg A hst
    simp only at h
    rw [hAg _ (hmem s hs), hAg _ (hmem t ht)] at h
    exact add_left_cancel h
  · intro τ hτ
    have h : g (y₀ + τ) ∈ g '' O := ⟨_, hmem τ hτ, rfl⟩
    rw [← hZV] at h
    exact h.1
  · simp [hgy₀]

end GroundTheory.Heights₂.Heights
