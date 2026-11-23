import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.SUnitsEulerDifference

noncomputable section

open Formalism.MainNotions.WeightAlgebra Formalism.BasicNotions NumberField IsDedekindDomain Module

namespace Formalism.MainNotions.Gaps.T0

variable {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ}

theorem thm0Concl_of (h : Thm0Local (D := D) (B := B) (P := P) (j := j)) :
    Thm0Concl (D := D) (B := B) (P := P) (j := j) := by
  intro large₂ X H S ka wL wF T nus β r hH1 hT hc hle hr hs hb hL
  refine ⟨r, hr, hs, hb, ?_⟩
  intro la e he V' hV
  have h0 : (0 : ℝ) ≤ (T : ℝ) * nus la := mul_nonneg (Nat.cast_nonneg _) (hH1.1 la)
  have he0 : (0 : ℤ) ≤ e := by
    have : (0 : ℝ) ≤ (e : ℝ) := h0.trans he
    exact_mod_cast this
  obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le he0
  have he' : (T : ℝ) * nus la ≤ (n : ℝ) := by simpa using he
  obtain ⟨L, hOk, herr⟩ := hL la n he'
  obtain ⟨h1, h2⟩ := h large₂ X H S ka wL wF T nus la n hH1 hT hc hle he' L hOk V' hV
  refine ⟨h1, ?_⟩
  have h3 : (((n : ℤ) : ℝ)) = (n : ℝ) := by simp
  rw [h3]
  linarith

end Formalism.MainNotions.Gaps.T0
