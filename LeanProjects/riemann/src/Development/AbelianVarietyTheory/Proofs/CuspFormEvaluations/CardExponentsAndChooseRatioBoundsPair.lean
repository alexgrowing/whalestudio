import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.BinomRatio
import ReciprocityTheory.SemistableReduction.FinrankRestrictTotalDegree

namespace GlobalTheory

theorem card_exponents_sum_lt_sub (D T : ℕ) (hT : D < T) :
    Nat.card {α : Fin D → ℕ // ∑ i, α i < T - D} = (T - 1).choose D := by
  have e : {α : Fin D →₀ ℕ // α.degree ≤ T - D - 1} ≃ {α : Fin D → ℕ // ∑ i, α i < T - D} :=
    Finsupp.equivFunOnFinite.subtypeEquiv fun α => by
      rw [Finsupp.degree_eq_sum]
      simp only [Finsupp.equivFunOnFinite_apply]
      omega
  rw [← Nat.card_congr e, ReciprocityTheory.MultiplicativeHeights.card_degree_le, show T - D - 1 + D = T - 1 by omega]

theorem le_of_add_mul_choose_pred_le (D T δ d ρ : ℕ) (hD : 2 ≤ D) (hT : 11 * D ^ 2 ≤ T)
    (hd : d ≤ δ * (T + 2 * D + 6).choose D) (hρ : ρ + δ * (T - 1).choose D ≤ d) :
    (ρ : ℝ) ≤ 22 * (D : ℝ) ^ 2 * d / T := by
  have hT' : D * (2 * D + 7) ≤ T := by nlinarith
  have hTpos : (0 : ℝ) < T := by
    have : 0 < T := by nlinarith
    exact_mod_cast this
  have key := ReciprocityTheory.ChartRestriction.G.T0.sub_mul_choose_le_mul_choose T D hT' D le_rfl
  have hd' : (d : ℝ) ≤ δ * (((T + 2 * D + 6).choose D : ℕ) : ℝ) := by exact_mod_cast hd
  have hρ' : (ρ : ℝ) + δ * (((T - 1).choose D : ℕ) : ℝ) ≤ d := by exact_mod_cast hρ
  have hTD : (0 : ℝ) ≤ (T : ℝ) - D * (2 * D + 7) := by
    have : ((D : ℝ) * (2 * D + 7)) ≤ T := by exact_mod_cast hT'
    linarith
  have hδ : (0 : ℝ) ≤ δ := Nat.cast_nonneg _
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg _
  have hD' : (2 : ℝ) ≤ D := by exact_mod_cast hD
  have s1 := mul_le_mul_of_nonneg_left key hδ
  have s2 := mul_le_mul_of_nonneg_left hd' hTD
  have s3 := mul_le_mul_of_nonneg_left hρ' hTpos.le
  have s4 : (D : ℝ) * (2 * D + 7) * d ≤ 22 * (D : ℝ) ^ 2 * d :=
    mul_le_mul_of_nonneg_right (by nlinarith) hd0
  rw [le_div_iff₀ hTpos]
  nlinarith

theorem card_exponents_and_choose_ratio_bounds : ∀ (D T : ℕ), (0 < D → D < T → Nat.card {α : Fin D → ℕ // ∑ i, α i < T - D} = (T - 1).choose D) ∧ ∀ (δ d ρ : ℕ), 2 ≤ D → 11 * D ^ 2 ≤ T → d ≤ δ * (T + 2 * D + 6).choose D → (ρ + δ * (T - 1).choose D ≤ d → (ρ : ℝ) ≤ 22 * (D : ℝ) ^ 2 * d / T) ∧ (ρ + δ * (T + D).choose D ≤ d → (ρ : ℝ) ≤ 22 * (D : ℝ) ^ 2 * d / T) := by
  intro D T
  refine ⟨fun _ h => card_exponents_sum_lt_sub D T h, fun δ d ρ hD hT hd =>
    ⟨le_of_add_mul_choose_pred_le D T δ d ρ hD hT hd, fun h => ?_⟩⟩
  refine le_of_add_mul_choose_pred_le D T δ d ρ hD hT hd (le_trans ?_ h)
  exact Nat.add_le_add_left (Nat.mul_le_mul_left _ (Nat.choose_le_choose D (by omega))) _

end GlobalTheory
