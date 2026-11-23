import Formalism.SharpRestriction.CuspSpanNormBounds.UnimodularSchurMeasures.CndHsLeDist
import Formalism.SharpRestriction.CuspSpanNormBounds.UnimodularSchurMeasures.CndDiamOfProved

noncomputable section

namespace Formalism.MainNotions.LeviCoordinates

open MeasureTheory NumberField Matrix Finset
open scoped InnerProductSpace ComplexOrder ENNReal
open Formalism.MainNotions.S Formalism.MainNotions.PlaceDegreeData Formalism.MainNotions.BridgeLemma

theorem cnd_far_deep (C Cq : ℝ) (hC : 1 ≤ C) (hCq : 0 ≤ Cq) (hCC : 16 * Cq ≤ C) :
    ∃ C₁₀ : ℝ, 1 ≤ C₁₀ ∧ ∀ C₁ ≥ C₁₀, ∀ (X : CData) (S : CSize X) (volK : ℝ) (n₀ : ℕ) (A : ℝ), 1 ≤ n₀ → X.HypB n₀ A →
      1 ≤ X.qq → X.FinVol → S.Strata → S.SepStep → S.DeepStepsQ volK C Cq →
      X.FarCount (X.Acnt C₁) (2 * (X.I.n : ℝ) ^ 2) (S.Mod C₁) ∧ ∀ A₁ : ℝ, 1 ≤ A₁ → X.DeepInt A₁ (S.Mod C₁) := by
  obtain ⟨C₁₀, h1, h⟩ := cnd_deepP C Cq hC hCq hCC
  refine ⟨C₁₀, h1, fun C₁ hC₁ X S volK n₀ A hn₀ hX hq hV hst hsep hS => ⟨?_, ?_⟩⟩
  · have hn : 1 ≤ X.I.n := le_trans hn₀ hX.1.1
    exact cnd_far S C₁ hn (cnd_two_le_Y X hn₀ hX) hst (cnd_pack S hn hst hsep)
  · exact h C₁ hC₁ X S volK n₀ A hn₀ hX hq hV hst hS

end Formalism.MainNotions.LeviCoordinates

end
