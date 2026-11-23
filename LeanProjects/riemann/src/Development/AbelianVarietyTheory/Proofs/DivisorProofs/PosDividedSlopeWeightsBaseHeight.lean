import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DividedWeightUnique
import Formalism.MeanHeightDescent.CovolumeFullAssemblyWeighted
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DividedWeightEntriesSignsSizes
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DividedWeightGapsBlockAndBarStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightDivisionL1BoundStatement

open Formalism.BasicNotions Formalism.BasicNotions.DV Formalism.MainNotions Formalism.L2.Indef.Tree NumberField GlobalTheory.MeanTop

namespace GlobalTheory.MeanTop.DividedSlope

theorem strictAnti_of_adj {N : ℕ} (v : Fin N → ℝ)
    (h : ∀ a b : Fin N, (b : ℕ) = a + 1 → v b < v a) : ∀ a b : Fin N, a < b → v b < v a := by
  intro a b hab
  obtain ⟨b, hb⟩ := b
  have hab' : (a : ℕ) < b := hab
  induction b, hab' using Nat.le_induction with
  | base => exact h a _ rfl
  | succ n hn ih =>
    have h1 := ih (by omega) (show (a : ℕ) < n from hn)
    have h2 := h ⟨n, by omega⟩ ⟨n + 1, hb⟩ rfl
    linarith

variable {ι : Type} [Fintype ι] {N : ℕ} (W : Wts ι N)

omit [Fintype ι] in
theorem T_pos (hW : W.Hyp) : (0 : ℝ) < W.T := by
  have := hW.h1
  have : 0 < W.T := by omega
  exact_mod_cast this

omit [Fintype ι] in
theorem pos_dividedSlopeWeights_baseHeight (hW : W.Hyp) : (0 : ℝ) < W.h0 := by
  have h1 := hW.h2.1
  have h2 := hW.weightConst_nonneg
  have : 0 < W.h0 := by omega
  exact_mod_cast this

omit [Fintype ι] in
theorem g_pos (hW : W.Hyp) : 0 < W.g := by
  have := T_pos W hW
  have := pos_dividedSlopeWeights_baseHeight W hW
  unfold Wts.g
  positivity

omit [Fintype ι] in
theorem g_le_of (hW : W.Hyp) {x : ℤ} (hx : W.h0 ≤ 4 * W.T * x) : W.g ≤ (x : ℝ) := by
  have hT := T_pos W hW
  have hx' : (W.h0 : ℝ) ≤ 4 * W.T * x := by exact_mod_cast hx
  unfold Wts.g
  rw [div_le_iff₀ (by positivity)]
  linarith

theorem adj_ge (hW : W.Hyp) (hD : W.IsDiv) (τ : ι) (a b : Fin N) (hab : (b : ℕ) = a + 1) (hb : W.p ≤ (b : ℕ)) :
    W.g ≤ reWt W.u' τ a - reWt W.u' τ b := by
  obtain ⟨-, h2, h3⟩ := GlobalTheory.T.dividedWeight_gaps_block_and_bar ι N W hW hD τ a b hab
  have hk := hW.kc_lt
  by_cases hp : (b : ℕ) = W.p
  · have := g_le_of W hW (h2 hp).2
    have ha : (a : ℕ) < W.p := by omega
    have hb' : ¬ (b : ℕ) < W.p := by omega
    simp only [reWt, Wts.u', ha, hb', if_true, if_false]
    push_cast at this ⊢
    linarith
  · have := g_le_of W hW (h3 hp (by omega))
    have ha : ¬ (a : ℕ) < W.p := by omega
    have hb' : ¬ (b : ℕ) < W.p := by omega
    simp only [reWt, Wts.u', ha, hb', if_false]
    push_cast at this ⊢
    linarith

theorem adj_lt (hW : W.Hyp) (hD : W.IsDiv) (τ : ι) (a b : Fin N) (hab : (b : ℕ) = a + 1) :
    reWt W.u' τ b < reWt W.u' τ a := by
  by_cases hb : W.p ≤ (b : ℕ)
  · have := adj_ge W hW hD τ a b hab hb
    have := g_pos W hW
    linarith
  · obtain ⟨h1, -, -⟩ := GlobalTheory.T.dividedWeight_gaps_block_and_bar ι N W hW hD τ a b hab
    have h := h1 (by omega)
    have h' : W.u1 τ b < W.u1 τ a := by omega
    have ha : (a : ℕ) < W.p := by omega
    have hb' : (b : ℕ) < W.p := by omega
    simp only [reWt, Wts.u', ha, hb', if_true]
    exact_mod_cast h'

theorem regular (hW : W.Hyp) (hD : W.IsDiv) (τ : ι) (a b : Fin N) (hab : a < b) :
    reWt W.u' τ b < reWt W.u' τ a :=
  strictAnti_of_adj _ (adj_lt W hW hD τ) a b hab

theorem anti (hW : W.Hyp) (hD : W.IsDiv) (τ : ι) (a b : Fin N) (hab : a ≤ b) :
    reWt W.u' τ b ≤ reWt W.u' τ a := by
  rcases hab.eq_or_lt with h | h
  · rw [h]
  · exact (regular W hW hD τ a b h).le

theorem far (hW : W.Hyp) (hD : W.IsDiv) (τ : ι) (a b : Fin N) (ha : W.p ≤ (a : ℕ)) (hab : a ≠ b) :
    W.g ≤ |reWt W.u' τ a - reWt W.u' τ b| := by
  have hk := hW.kc_lt
  rcases lt_or_gt_of_ne hab with h | h
  · have h' : (a : ℕ) < b := h
    have hb := b.2
    have h1 := adj_ge W hW hD τ a ⟨a + 1, by omega⟩ rfl (by simp only; omega)
    have h2 := anti W hW hD τ ⟨a + 1, by omega⟩ b (show (a : ℕ) + 1 ≤ b from h')
    exact le_trans (by linarith) (le_abs_self _)
  · have h' : (b : ℕ) < a := h
    have hb := a.2
    have h1 := adj_ge W hW hD τ ⟨a - 1, by omega⟩ a (by simp only; omega) ha
    have h2 := anti W hW hD τ b ⟨a - 1, by omega⟩ (show (b : ℕ) ≤ a - 1 by omega)
    exact le_trans (by linarith) (neg_le_abs _)

theorem entry_le (hW : W.Hyp) (hD : W.IsDiv) (τ : ι) (i : Fin N) :
    |reWt W.u' τ i| ≤ 2 * W.b / W.T := by
  have hT := T_pos W hW
  have h1 := (GlobalTheory.MeanTop.divided_entries ι N W hW hD τ i).1
  have h2 := (GlobalTheory.T.weight_division_l1_bound ι N W hW hD).2.2 τ i
  have h3 := hW.h5 τ i
  have h1' : ((W.T : ℝ) + W.Dd + 1) * |(W.u1 τ i : ℝ)| ≤ |(W.u τ i : ℝ)| + W.c0 + 4 * N := by exact_mod_cast h1
  have h2' : |(W.u' τ i : ℝ)| ≤ |(W.u1 τ i : ℝ)| := by exact_mod_cast h2
  have h4 : (0 : ℝ) ≤ W.Dd := Nat.cast_nonneg _
  have h5 := abs_nonneg (W.u1 τ i : ℝ)
  rw [le_div_iff₀ hT]
  show |(W.u' τ i : ℝ)| * W.T ≤ 2 * W.b
  nlinarith [mul_le_mul_of_nonneg_right h2' hT.le, mul_nonneg h4 h5]

end GlobalTheory.MeanTop.DividedSlope
