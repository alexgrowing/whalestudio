import Mathlib
import Formalism.SharpRestriction.Divisibility.LocalQuadraticParts
import Formalism.LocalRingCardinality.CoeNeZeroOfNotMem
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.OneLeLetterBlockLength

open Formalism.BasicNotions Formalism.BasicNotions.DV Formalism.MainNotions NumberField IsDedekindDomain

namespace GlobalTheory

theorem nuRow_zero_le (D : D7) (u : D.what₂.Word) (j : ℕ) (τ : D.what₂.Tau) (hk : 0 < D.R.k) :
    nuRow D u j τ 0 ≤ ((((D.hcW u τ).u ⟨0, hk⟩ : ℚ)) : ℝ) + wSz D j τ := by
  unfold nuRow srcPar
  rw [dif_pos hk]
  have h1 : 1 ≤ D.R.N j := by unfold Ranks.N; omega
  have h1' : (1 : ℝ) ≤ D.R.N j := by exact_mod_cast h1
  have h2 : (0 : ℝ) ≤ D.R.N (j - 1) := Nat.cast_nonneg _
  push_cast
  linarith

theorem nuRow_nonneg_le_ten_mul : ∀ (eps : ℝ) (Fm : FamP eps), (∃ x0 : ℝ, ∀ x ≥ x0, Fm.x1 < x → ∀ i : Fm.Ix x, ∀ u, ∀ j ∈ SizeData₂.lifts (Fm.D x i), ∀ τ, ∀ l < (Fm.D x i).R.N (j - 1), 0 ≤ nuRow (Fm.D x i) u j τ l ∧ nuRow (Fm.D x i) u j τ l ≤ 10 * x * (Fm.L x i).sc.b) := by
  intro eps Fm
  obtain ⟨x0, h⟩ := GlobalTheory.HCEntries.entries eps Fm
  refine ⟨x0, fun x hx hx1 i u j hj τ l hl => ?_⟩
  obtain ⟨hw, hu, -⟩ := h x hx hx1 i
  obtain ⟨-, hw3, hwe⟩ := hw j hj τ
  have hj' := Finset.mem_Icc.1 hj
  obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
  have hl' : l < (Fm.D x i).R.N j' := by simpa using hl
  have hjm : j' < (Fm.D x i).R.m := by omega
  have hk : 0 < (Fm.D x i).R.k := by have := (Fm.D x i).R.m_add_three_le_k; omega
  refine ⟨(RowWeightLemmas.nuRow_pos _ u j' hjm τ l hl').le, ?_⟩
  have h1 := RowWeightLemmas.nuRow_anti' _ u j' hjm τ l 0 (Nat.zero_le _) hl'
  have h2 := nuRow_zero_le (Fm.D x i) u (j' + 1) τ hk
  have h3 := (abs_le.1 (hu u τ ⟨0, hk⟩)).2
  have hb : 0 < (Fm.L x i).sc.b := Real.exp_pos _
  have hx' : 1 < x := Fm.one_lt_family_threshold.trans hx1
  have h4 : (Fm.L x i).sc.b ≤ x * (Fm.L x i).sc.b := le_mul_of_one_le_left hb.le hx'.le
  nlinarith

end GlobalTheory
