import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.DivAddLogbLeEightMulErrorScale

noncomputable section

namespace Formalism.MainNotions.N.FrobeniusPowerSeries
namespace ArcLengthThreeFiltration

theorem numerics (l b w S η b₁ w' σ A : ℕ) (hl : 11 ≤ l) (hη20 : 20 * η ≤ b) (hS20 : 20 * S ≤ b)
    (hw20 : 20 * w ≤ b) (hb₁ : b ≤ b₁) (hw' : w' ≤ w) (hηw' : η < w')
    (hy : l * (w' + S + η) ≤ b₁)
    (hσ : (σ : ℝ) ≤ 3 * Sg l (b + η + S) w S η)
    (hA : (A : ℝ) ≤ (((b + η + S : ℕ) : ℝ) + η) / ((l : ℝ) - 1) + 1)
    (hsm : 40 * Sg l (b + η + S) w S η ≤ (b : ℝ) / 4) :
    ∃ s₁ : ℕ, 2 * σ < s₁ ∧ A + s₁ - 1 < b₁ - η ∧
      ¬ (((s₁ : ℝ) - 2 * σ) ≤ max 0 (((w' + S + η : ℕ) : ℝ) - ((b₁ - η - (A + s₁ - 1) : ℕ) : ℝ) / l + 2 +
        Real.logb l ((w' + S + η : ℕ) : ℝ))) ∧
      (s₁ : ℝ) ≤ 10 * Sg l (b + η + S) w S η := by
  have hw1 : 1 ≤ w' := by omega
  have hb : 1 ≤ b := by omega
  have hl0 : (0 : ℝ) < l := by
    have : (11 : ℝ) ≤ l := by exact_mod_cast hl
    linarith
  obtain ⟨s₁, hs₁def⟩ : ∃ s₁ : ℕ, s₁ = ⌊(11 / 10 : ℝ) * (2 * (σ : ℝ) + ((η : ℝ) + (A : ℝ)) / l + 2 +
      Real.logb l (2 * ((b + η + S : ℕ) : ℝ)))⌋₊ + 1 := ⟨_, rfl⟩
  have hs1 : 1 ≤ s₁ := by rw [hs₁def]; omega
  have hlt : (11 / 10 : ℝ) * (2 * (σ : ℝ) + ((η : ℝ) + (A : ℝ)) / l + 2 +
      Real.logb l (2 * ((b + η + S : ℕ) : ℝ))) < (s₁ : ℝ) := by
    rw [hs₁def]; push_cast; exact Nat.lt_floor_add_one _
  have hten : (s₁ : ℝ) ≤ 10 * Formalism.MainNotions.N.FrobeniusPowerSeries.Sg l (b + η + S) w S η := by
    rw [hs₁def]
    exact Formalism.MainNotions.N.FrobeniusPowerSeries.floor_succ_le_ten_mul_errorScale l hl b w S η hb hη20 hS20 hw20 (σ : ℝ) (A : ℝ)
      (Nat.cast_nonneg _) hσ (Nat.cast_nonneg _) hA
  have hsub := Formalism.MainNotions.N.FrobeniusPowerSeries.one_le_sub_sub_sub l hl b w S η b₁ hb hη20 hS20 hw20 hb₁ hsm (A : ℝ) (s₁ : ℝ) hA hten
  have hnat : A + s₁ + η ≤ b₁ := by
    have : (A : ℝ) + s₁ + η ≤ b₁ := by linarith
    exact_mod_cast this
  have e : (b₁ - η - (A + s₁ - 1) : ℕ) + η + A + s₁ = b₁ + 1 := by omega
  have hcast : ((b₁ - η - (A + s₁ - 1) : ℕ) : ℝ) = (b₁ : ℝ) - η - A - s₁ + 1 := by
    have := congrArg (fun n : ℕ => (n : ℝ)) e
    push_cast at this
    linarith
  have hlog : 0 ≤ Real.logb l (2 * ((b + η + S : ℕ) : ℝ)) :=
    Formalism.MainNotions.N.FrobeniusPowerSeries.CaseA.logb_nn l (b + η + S) hl (by omega)
  have hq : 0 ≤ ((η : ℝ) + (A : ℝ)) / l := div_nonneg (by positivity) hl0.le
  have hσ0 : (0 : ℝ) ≤ σ := Nat.cast_nonneg _
  have hσ2 : 2 * (σ : ℝ) < s₁ := by linarith
  have hyl : ((w' + S + η : ℕ) : ℝ) ≤ (b₁ : ℝ) / l := by
    rw [le_div_iff₀ hl0]
    have hy' : (w' + S + η) * l ≤ b₁ := by rw [Nat.mul_comm]; exact hy
    exact_mod_cast hy'
  have hy2 : ((w' + S + η : ℕ) : ℝ) ≤ 2 * ((b + η + S : ℕ) : ℝ) := by
    exact_mod_cast (by omega : w' + S + η ≤ 2 * (b + η + S))
  have hy1 : (1 : ℝ) ≤ ((w' + S + η : ℕ) : ℝ) := by
    exact_mod_cast (by omega : 1 ≤ w' + S + η)
  have key := Formalism.MainNotions.N.FrobeniusPowerSeries.not_le_max_of_lt l hl (b + η + S) (by omega) (σ : ℝ) (A : ℝ) (s₁ : ℝ) (η : ℝ) (b₁ : ℝ)
    ((w' + S + η : ℕ) : ℝ) hσ0 (Nat.cast_nonneg _) (Nat.cast_nonneg _) hy1 hyl hy2 hlt
  refine ⟨s₁, ?_, by omega, ?_, hten⟩
  · exact_mod_cast hσ2
  · rw [hcast]; exact key

end ArcLengthThreeFiltration
end Formalism.MainNotions.N.FrobeniusPowerSeries
