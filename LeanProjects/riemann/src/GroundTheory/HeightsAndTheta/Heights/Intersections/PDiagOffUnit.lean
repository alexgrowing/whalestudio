import Mathlib
import GroundTheory.HeightsAndTheta.Heights.Intersections.StatementsDiagOffPair
import GroundTheory.HeightsAndTheta.Heights.Intersections.PDiagForms
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI

noncomputable section

open DiagonalForms in

theorem DiagOffUnit.proof (hF : DiagOffFrame.Statement) (hM : DiagOffMinor.Statement) :
    DiagOffUnit.Statement := by
  intro Ω _ ι ν κ _ _ _ E _ _ Φ _ _ x B e φ δ hsec hgen hdet hx a ha W hW hrel hPW hΔ
  obtain ⟨i, l, k, k', hfr⟩ := hF Ω ι ν κ E Φ x B e φ δ hsec hgen hdet hx a ha W hW hrel hPW
  have hQ : lineMinor k k' ∉ W := fun hQ =>
    hΔ (hM Ω ι ν κ E Φ x B e φ δ hsec hgen hdet hx a ha W hW hrel hPW i l k k' hfr hQ)
  obtain ⟨hXi, hXl, N, F, hFd, hFv, hFW⟩ := hfr
  refine ⟨T.wwDeg (N + 3) 0, T.wwDeg N 1, F,
    (X ⟨T.WBlk.base, i⟩ : MRing (T.wwIdx ι ν κ)) ^ N * X ⟨T.WBlk.det, l⟩ * lineMinor k k', hFd, ?_, ?_, hFW,
    ?_, ?_⟩
  · unfold lineMinor
    have := isMultiHomog_mul
      (isMultiHomog_mul (isMultiHomog_pow (isMultiHomog_X (ι := T.wwIdx ι ν κ) T.WBlk.base i) N)
        (isMultiHomog_X (ι := T.wwIdx ι ν κ) T.WBlk.det l))
      (isMultiHomog_sub
        (isMultiHomog_mul (isMultiHomog_X (ι := T.wwIdx ι ν κ) T.WBlk.line0 k)
          (isMultiHomog_X (ι := T.wwIdx ι ν κ) T.WBlk.line1 k'))
        (isMultiHomog_mul (isMultiHomog_X (ι := T.wwIdx ι ν κ) T.WBlk.line0 k')
          (isMultiHomog_X (ι := T.wwIdx ι ν κ) T.WBlk.line1 k)))
    refine isMultiHomog_of_eq this ?_
    funext b
    cases b <;> simp [T.wwDeg]
  · intro b
    cases b <;> simp [T.wwDeg]
  · intro hv
    rcases hW.mem_or_mem hv with h | h
    · rcases hW.mem_or_mem h with h | h
      · exact hXi (hW.mem_of_pow_mem _ h)
      · exact hXl h
    · exact hQ h
  · rw [hFv]
    simp only [lineMinor, map_mul, map_sub, map_pow, aeval_X]
    show algebraMap Ω Φ (x i) ^ N * algebraMap Ω Φ (δ l) * algebraMap Ω Φ (dualMinor e φ k k') * T.diagSec a =
      algebraMap Ω Φ (x i) ^ N * algebraMap Ω Φ (δ l) *
        (T.lineVal e (φ k) (a 0) * T.lineVal e (φ k') (a 1) - T.lineVal e (φ k') (a 0) * T.lineVal e (φ k) (a 1))
    rw [lineVal_cross, T.diagSec, dualMinor]
    ring

end

end GroundTheory.Heights₂.Heights.Inter
