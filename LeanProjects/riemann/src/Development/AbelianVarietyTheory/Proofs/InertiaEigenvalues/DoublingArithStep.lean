import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NoTowerQ
open Formalism.BasicNotions Formalism.BasicNotions.Loc ValuativeRel GroundTheory.LocalField GlobalTheory.PMon.Ram

namespace GlobalTheory.PMon.Ram

theorem doublingArith_step (V : ℕ → ℕ → ℕ) (E k : ℕ) (hE : 0 < E)
    (h1 : ∀ j, 1 ≤ j → j + 1 ≤ 8 → min (2 * V k (k + j)) (V k (k + j) + E) ≤ V k (k + j + 1))
    (h2 : V k (k + 8) ≤ 6 * E)
    (h3 : V k (k + 3) ≤ V k (k + 2) + V (k + 2) (k + 3)) :
    V k (k + 1) < E ∧ 2 * V k (k + 1) ≤ V (k + 2) (k + 3) := by
  have e1 := h1 1 le_rfl (by norm_num)
  have e2 := h1 2 (by norm_num) (by norm_num)
  have e3 := h1 3 (by norm_num) (by norm_num)
  have e4 := h1 4 (by norm_num) (by norm_num)
  have e5 := h1 5 (by norm_num) (by norm_num)
  have e6 := h1 6 (by norm_num) (by norm_num)
  have e7 := h1 7 (by norm_num) (by norm_num)
  rw [show k + 1 + 1 = k + 2 by ring] at e1
  rw [show k + 2 + 1 = k + 3 by ring] at e2
  rw [show k + 3 + 1 = k + 4 by ring] at e3
  rw [show k + 4 + 1 = k + 5 by ring] at e4
  rw [show k + 5 + 1 = k + 6 by ring] at e5
  rw [show k + 6 + 1 = k + 7 by ring] at e6
  rw [show k + 7 + 1 = k + 8 by ring] at e7
  rw [min_le_iff] at e1 e2 e3 e4 e5 e6 e7
  omega

theorem doublingArith : ∀ (V : ℕ → ℕ → ℕ) (E T g : ℕ), 0 < E →
    (∀ k ≤ 2 * T, ∀ j, 1 ≤ j → j + 1 ≤ 8 → min (2 * V k (k + j)) (V k (k + j) + E) ≤ V k (k + j + 1)) →
    (∀ k ≤ 2 * T, V k (k + 8) ≤ 6 * E) →
    (∀ k, V k (k + 3) ≤ V k (k + 2) + V (k + 2) (k + 3)) → g ≤ V 0 1 → 2 ^ T * g < E := by
  intro V E T g hE h1 h2 h3 hg
  have step : ∀ k, k ≤ 2 * T → V k (k + 1) < E ∧ 2 * V k (k + 1) ≤ V (k + 2) (k + 3) :=
    fun k hk => doublingArith_step V E k hE (h1 k hk) (h2 k hk) (h3 k)
  have ind : ∀ i, i ≤ T → 2 ^ i * g ≤ V (2 * i) (2 * i + 1) := by
    intro i
    induction i with
    | zero => intro _; simpa using hg
    | succ n ih =>
      intro hn
      have hs := (step (2 * n) (by omega)).2
      have ih' := ih (by omega)
      rw [show 2 * (n + 1) = 2 * n + 2 by ring, show 2 * n + 2 + 1 = 2 * n + 3 by ring, pow_succ]
      calc 2 ^ n * 2 * g = 2 * (2 ^ n * g) := by ring
        _ ≤ 2 * V (2 * n) (2 * n + 1) := Nat.mul_le_mul_left 2 ih'
        _ ≤ V (2 * n + 2) (2 * n + 3) := hs
  exact lt_of_le_of_lt (ind T le_rfl) (step (2 * T) le_rfl).1

end GlobalTheory.PMon.Ram
