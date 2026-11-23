import Formalism.SharpRestriction.GrowthBounds.ColumnSpanDensity.TheoremIOfLatticeFunctorComparison

namespace Formalism.MainNotions.flipOneThree.Pf

open Formalism.MainNotions.G Formalism.MainNotions.flipOneThree

theorem ClosedA.mono {P Q : ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → Prop} (h : ClosedA P)
    (hPQ : ∀ a b c d e f g i j k, P a b c d e f g i j k → Q a b c d e f g i j k) : ClosedA Q := by
  intro Cc hCc
  obtain ⟨T0, hT0, h0⟩ := h Cc hCc
  refine ⟨T0, hT0, fun C₀ hC₀ => ?_⟩
  obtain ⟨T1, hT1, h1⟩ := h0 C₀ hC₀
  refine ⟨T1, hT1, fun CE1 CE2 Cm a1 a2 a3 => ?_⟩
  obtain ⟨T2, hT2, h2⟩ := h1 CE1 CE2 Cm a1 a2 a3
  refine ⟨T2, hT2, fun CH hCH => ?_⟩
  obtain ⟨CA, Ckap, Ct, Cs, b1, b2, b3, b4, hP⟩ := h2 CH hCH
  exact ⟨CA, Ckap, Ct, Cs, b1, b2, b3, b4, hPQ _ _ _ _ _ _ _ _ _ _ hP⟩

theorem ClosedP.mono {P Q : ℝ → ℝ → ℝ → Prop} (h : ClosedP P) (hPQ : ∀ a b c, P a b c → Q a b c) : ClosedP Q := by
  obtain ⟨T0, hT0, h0⟩ := h
  refine ⟨T0, hT0, fun C₀ hC₀ => ?_⟩
  obtain ⟨T2, C, hT2, hC, h1⟩ := h0 C₀ hC₀
  exact ⟨T2, C, hT2, hC, fun CH hCH => hPQ _ _ _ (h1 CH hCH)⟩

end Formalism.MainNotions.flipOneThree.Pf
