import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.APrime
import GroundTheory.HeightsAndTheta.Heights.Intersections.StatementsAntisym
import GroundTheory.HeightsAndTheta.Heights.Intersections.ProjLineRankTwoPushforwardHypotheses
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Inter

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4

theorem yyBlockMap_thm : YYBlockMapStatement := by
  intro ι ν κ j
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro a b h
    fin_cases j <;> cases a <;> cases b <;> simp_all [diagonalBlockIndex]
  · rintro ⟨a, x⟩ ⟨b, y⟩ h
    fin_cases j <;> cases a <;> cases b <;> simp [T.yyEmb] at h <;> injection h with h1 h2 <;>
      first | (cases h2; rfl) | cases h1
  · rintro ⟨a, x⟩
    fin_cases j <;> cases a <;> rfl
  · rintro ⟨b, y⟩ ⟨a, ha⟩
    fin_cases j <;> cases a <;> cases b <;>
      first
        | (refine ⟨⟨.base, y⟩, ?_⟩; simp [T.yyEmb]; done)
        | (refine ⟨⟨.det, y⟩, ?_⟩; simp [T.yyEmb]; done)
        | (refine ⟨⟨.line, y⟩, ?_⟩; simp [T.yyEmb]; done)
        | simp [diagonalBlockIndex] at ha

theorem PropAPrime.proof (h₁ : ToFibreSquare.Statement) (h₂ : FibreInt.Statement) : PropAPrime.Statement := by
  intro I hI D S X A hX hAs hAb k hk hkD
  have hb := yyBlockMap_thm S.ι S.ν S.κ
  have p0 := IndefiniteRowSideFullHecke.Inter.isPullHerm_pullHerm (hb 0) X
  have p1 := IndefiniteRowSideFullHecke.Inter.isPullHerm_pullHerm (hb 1) X
  have pA := IndefiniteRowSideFullHecke.Inter.isPullHerm_pullHerm (hb 0) A
  obtain ⟨F, hFI, hFΦ⟩ := h₁ I hI D S X A _ _ _ hX hAs hAb p0 p1 pA
  have hfib := h₂ D S X A _ _ _ hX hAs hAb p0 p1 pA k hk hkD
  have hF := aPrime_thm D F k hk hkD
  rw [hFI (2 * k) (by omega),
    Finset.sum_congr rfl (fun i hi => hFΦ k i hk hkD (Finset.mem_range.1 hi)), ← Finset.mul_sum, hfib,
    ← mul_neg] at hF
  exact mul_left_cancel₀ (by positivity) hF

end GroundTheory.Heights₂.Heights.Inter
