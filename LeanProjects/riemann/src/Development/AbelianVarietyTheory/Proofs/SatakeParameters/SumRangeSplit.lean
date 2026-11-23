import Mathlib
import Formalism.SharpRestriction.ParConsts
import Formalism.LocalRingCardinality.DataKerI
import Formalism.LocalRingCardinality.CoeNeZeroOfNotMem
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ScaleFamilySizeRelationsEventually
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.BTLeFiveQuarters
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.NotMemTopPlaces
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.TopRowsParams
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.BlockRowsMemIcc
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.YoungDiagramCardEqSumRowLenRange

open Formalism.MainNotions Formalism.BasicNotions Formalism.MainNotions.G Classical

namespace GlobalTheory.TopExcess

theorem sum_range_split (f : ℕ → ℝ) (k M : ℕ) (hk : 2 ≤ k) :
    ∑ r ∈ Finset.range (k + M), f r =
      f 0 + ∑ r ∈ Finset.Ico 1 (k - 1), f r + f (k - 1) + ∑ r ∈ Finset.Ico k (k + M), f r := by
  obtain ⟨n, rfl⟩ : ∃ n, k = n + 1 := ⟨k - 1, by omega⟩
  rw [Nat.add_sub_cancel, ← Finset.sum_range_add_sum_Ico f (Nat.le_add_right (n + 1) M), Finset.sum_range_succ,
    ← Finset.sum_range_add_sum_Ico f (by omega : 1 ≤ n), Finset.sum_range_one]

theorem sum_Ico_bounds (f : ℕ → ℝ) (a b : ℕ) (lo hi : ℝ) (h : ∀ r, a ≤ r → r < b → lo ≤ f r ∧ f r ≤ hi) :
    ((b - a : ℕ) : ℝ) * lo ≤ ∑ r ∈ Finset.Ico a b, f r ∧ ∑ r ∈ Finset.Ico a b, f r ≤ ((b - a : ℕ) : ℝ) * hi := by
  constructor
  · have := Finset.card_nsmul_le_sum (Finset.Ico a b) f lo
      (fun r hr => (h r (Finset.mem_Ico.1 hr).1 (Finset.mem_Ico.1 hr).2).1)
    rwa [Nat.card_Ico, nsmul_eq_mul] at this
  · have := Finset.sum_le_card_nsmul (Finset.Ico a b) f hi
      (fun r hr => (h r (Finset.mem_Ico.1 hr).1 (Finset.mem_Ico.1 hr).2).2)
    rwa [Nat.card_Ico, nsmul_eq_mul] at this

theorem top_excess : ∀ {eps : ℝ} (Fm : FamP eps), ∃ x0 : ℝ, ∀ x ≥ x0, Fm.x1 < x → ∀ i : Fm.Ix x, ∀ (u : (Fm.D x i).what₂.Word), ∀ j < (Fm.D x i).R.m, ∀ (z : Bool × HH (Fm.D x i)), IsTopPl (Fm.D x i) z → 0 ≤ (((nuD (Fm.D x i) u j z).card : ℕ) : ℝ) - (((nuD (Fm.D x i) u j z).rowLen 0 : ℕ) : ℝ) - ((((Fm.D x i).R.k : ℝ) - 1) * wPl (Fm.D x i) (j + 1) z - 2 * wPl (Fm.D x i) (j + 1) z) ∧ (((nuD (Fm.D x i) u j z).card : ℕ) : ℝ) - (((nuD (Fm.D x i) u j z).rowLen 0 : ℕ) : ℝ) - ((((Fm.D x i).R.k : ℝ) - 1) * wPl (Fm.D x i) (j + 1) z - 2 * wPl (Fm.D x i) (j + 1) z) ≤ 4 * wPl (Fm.D x i) (j + 1) z := by
  intro eps Fm
  obtain ⟨x1, h1⟩ := GlobalTheory.ShNums.size_rel Fm
  obtain ⟨x2, h2⟩ := GlobalTheory.Ggeo.wPl_windows Fm
  obtain ⟨x3, h3⟩ := GlobalTheory.LongRows.longRows Fm
  obtain ⟨x4, h4⟩ := GlobalTheory.TopRows.top_rows Fm
  obtain ⟨x5, h5⟩ := GlobalTheory.blockRows_mem_Icc Fm
  refine ⟨max (max (max x1 x2) (max x3 x4)) x5, fun x hx hx1 i u j hj z hz => ?_⟩
  simp only [ge_iff_le, max_le_iff] at hx
  obtain ⟨⟨⟨g1, g2⟩, g3, g4⟩, g5⟩ := hx
  obtain ⟨a1, a2, a3, -, a5, a6, -, -, a9, -⟩ := h1 x g1 hx1 i
  obtain ⟨b1, -, b3⟩ := h2 x g2 hx1 i j hj z
  obtain ⟨b3, -⟩ := b3 hz
  have c := h3 x g3 hx1 i u j hj z
  obtain ⟨-, -, d3, d4⟩ := h4 x g4 hx1 i u j hj z hz
  have e := h5 x g5 hx1 i u j hj z
  clear h1 h2 h3 h4 h5
  generalize Fm.L x i = L at *
  generalize Fm.D x i = D at *
  have hk : 5 ≤ D.R.k := by have := D.R.m_add_three_le_k; have := D.R.two_le_m; omega
  have hN : D.R.N j = D.R.k + j * (D.R.t + 1) := by unfold Ranks.N; omega
  have hok := nuRowOK D
  rw [GlobalTheory.nuD_card_eq_sum_nuRow D hok u j hj z, hok u j hj z 0, if_pos (by omega), hN,
    sum_range_split _ _ _ (by omega)]
  obtain ⟨m1, m2⟩ := sum_Ico_bounds (DV.nuRow D u (j + 1) (tauPl D z)) 1 (D.R.k - 1) _ _
    (fun r hr1 hr2 => let h := (c r (by omega)).2 hz hr1 (by omega); ⟨h.1.le, h.2.le⟩)
  obtain ⟨n1, n2⟩ := sum_Ico_bounds (DV.nuRow D u (j + 1) (tauPl D z)) D.R.k (D.R.k + j * (D.R.t + 1)) _ _
    (fun r hr1 hr2 => e r hr1 (by omega))
  have hkc : ((D.R.k - 1 - 1 : ℕ) : ℝ) = (D.R.k : ℝ) - 2 := by
    rw [Nat.sub_sub, Nat.cast_sub (by omega)]; norm_num
  rw [hkc] at m1 m2
  rw [Nat.add_sub_cancel_left] at n1 n2
  push_cast at n1 n2
  have hS := L.Sc_pos
  have he := L.etaSz_pos
  have hk' : (5 : ℝ) ≤ D.R.k := by exact_mod_cast hk
  have hj' : (j : ℝ) ≤ D.R.m := by exact_mod_cast hj.le
  have ht : (0 : ℝ) ≤ D.R.t := Nat.cast_nonneg _
  have hNm : (0 : ℝ) ≤ D.R.N D.R.m := Nat.cast_nonneg _
  have hx0 : 0 < L.sc.x := by linarith
  have hb : 0 < L.sc.b := Real.exp_pos _
  have hb' : 0 < L.sc.b' := div_pos (mul_pos hx0 hb) (Real.exp_pos _)
  have hq : L.sc.b' / L.sc.x ≤ L.sc.b' / 4 := div_le_div_of_nonneg_left hb'.le (by norm_num) a6
  have hbl : (j : ℝ) * ((D.R.t : ℝ) + 1) * L.etaSz ≤ (D.R.m : ℝ) * ((D.R.t : ℝ) + 1) * L.etaSz := by gcongr
  have hS1 : L.Sc ≤ (D.R.k : ℝ) * L.Sc := le_mul_of_one_le_left hS.le (by linarith)
  rw [mul_div_assoc] at d4
  constructor <;> nlinarith

end GlobalTheory.TopExcess
