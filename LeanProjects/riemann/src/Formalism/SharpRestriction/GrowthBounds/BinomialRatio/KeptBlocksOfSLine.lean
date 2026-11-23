import Formalism.SharpRestriction.GrowthBounds.BinomialRatio.KeptBlocksOfUSLines

noncomputable section

namespace Formalism.MainNotions.ColumnSystems.Pf

open Formalism.MainNotions.G

theorem pairC_le_sum {s r : ℕ} {A : ℕ} {Ai Ci : Fin s → ℕ} {mu : Fin (2 * s + 1 + 1) → Fin (r + 1) → ℤ}
    (h : IsChain (kLetters A Ai Ci) mu) : ∀ i : Fin s,
      ((pairC mu i.val : ℤ) : ℝ) ≤ (A : ℝ) + ∑ l : Fin s, if l.val < i.val then (Ai l : ℝ) else 0 := by
  intro ⟨i, hi⟩
  induction i with
  | zero =>
    rw [pairC_zero h]
    simp
  | succ i ih =>
    have ih' := ih (by omega)
    obtain ⟨-, -, t3, -, t5, -, -, -⟩ := pair_top h ⟨i, by omega⟩
    have eO : pairO mu Ai ⟨i, by omega⟩ = pairW mu i + pairSg mu Ai ⟨i, by omega⟩ := by unfold pairSg; ring
    have t3' : (0 : ℤ) ≤ pairW mu i := t3
    have hO : (0 : ℤ) ≤ pairO mu Ai ⟨i, by omega⟩ := by rw [eO]; omega
    have eC : pairC mu (i + 1) = pairC mu i + (Ai ⟨i, by omega⟩ : ℤ) - pairO mu Ai ⟨i, by omega⟩ := by
      unfold pairO; ring
    have e : (∑ l : Fin s, if l.val < i + 1 then (Ai l : ℝ) else 0) =
        (∑ l : Fin s, if l.val < i then (Ai l : ℝ) else 0) + (Ai ⟨i, by omega⟩ : ℝ) := by
      have h2 : (∑ l : Fin s, if l = (⟨i, by omega⟩ : Fin s) then (Ai l : ℝ) else 0) = (Ai ⟨i, by omega⟩ : ℝ) := by simp
      rw [← h2, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun l _ => ?_
      by_cases h1 : l.val < i
      · rw [if_pos (by omega), if_pos h1, if_neg (fun h => by rw [h] at h1; simp at h1)]; ring
      · by_cases h3 : l.val = i
        · rw [if_pos (by omega), if_neg h1, if_pos (Fin.ext h3)]; ring
        · rw [if_neg (by omega), if_neg h1, if_neg (fun h => h3 (by rw [h]))]; ring
    show ((pairC mu (i + 1) : ℤ) : ℝ) ≤ _
    rw [eC, e]
    have hOr : (0 : ℝ) ≤ ((pairO mu Ai ⟨i, by omega⟩ : ℤ) : ℝ) := by exact_mod_cast hO
    push_cast
    linarith

theorem pairU_at {C0 CYb Cde Ck CD Cb CE1 CE2 Cc : ℝ}
    (hstd : ∀ X : Loc, D1num X → HIext C0 CYb Cde Ck CD Cb X → CBound Cc X → Std C0 Cde CE1 CE2 1 X) :
    PairUAt C0 CYb Cde Ck CD Cb CE1 CE2 Cc := by
  intro X _ hD hI hc j rz ry hd A hA1 hA2 mu lam hP hK i hi
  have hs := hstd X hD hI hc
  have hk5 := hs.k5
  have hk : (0 : ℝ) < X.k := by linarith
  have hkk : X.k = (X.m : ℝ) + 1 := rfl
  have hLK := hs.LaK
  have hN1 : (1 : ℝ) ≤ X.N1 := by exact_mod_cast hs.N1pos
  have hLa1 := hs.La1

  have hdich := (coarse_degree_alternative le_rfl hs j (digitBlock rz ry) hd i).2 hi
  set Ai := (clA C0 CE1 CE2 X j rz ry i : ℝ) with hAi
  have hdich' : ((X.seg C0 CE1 CE2 j).A0 X.p : ℝ) < Ai * (1 - X.de C0 Cde) := hdich

  have hn4 := coarse_degree_prefix_sum hs le_rfl j rz ry hd i
  have hc := pairC_le_sum hP.1 i
  have hp2 : 4 / (X.p : ℝ) ^ 2 ≤ X.de C0 Cde / 2 := by
    have hpk := hs.pk
    have hY := hs.Y1
    have hp0 : (0 : ℝ) < X.p := by have := hs.p5; exact_mod_cast (show 0 < X.p by omega)
    have hY2 : (1 : ℝ) ≤ X.Y ^ 2 := one_le_pow₀ hY
    have h1 : X.k ^ 2 ≤ (X.p : ℝ) := le_trans (by nlinarith [mul_le_mul_of_nonneg_left hY2 (sq_nonneg X.k)]) hpk
    have h2 : X.k ^ 4 ≤ (X.p : ℝ) ^ 2 := by nlinarith
    have h3 : 40 / X.k ≤ X.de C0 Cde := by
      refine le_trans ?_ hLK
      rw [div_le_div_iff_of_pos_right hk]
      nlinarith
    have h4 : 4 / (X.p : ℝ) ^ 2 ≤ 4 / X.k ^ 4 := div_le_div_of_nonneg_left (by norm_num) (by positivity) h2
    have h5 : 4 / X.k ^ 4 ≤ 20 / X.k := by
      rw [div_le_div_iff₀ (by positivity) hk]
      have hk3 : (1 : ℝ) ≤ X.k ^ 3 := one_le_pow₀ (by linarith)
      have e : X.k ^ 4 = X.k * X.k ^ 3 := by ring
      rw [e]
      nlinarith [mul_le_mul_of_nonneg_left hk3 hk.le]
    have h3' : 20 / X.k ≤ X.de C0 Cde / 2 := by
      have e : 20 / X.k = (40 / X.k) / 2 := by ring
      rw [e]
      linarith
    linarith
  have hAi0 : (0 : ℝ) ≤ Ai := Nat.cast_nonneg _
  have hci : ((pairC mu i.val : ℤ) : ℝ) ≤ Ai * (1 - X.de C0 Cde / 2) := by
    have e4 : 4 * Ai / (X.p : ℝ) ^ 2 = Ai * (4 / (X.p : ℝ) ^ 2) := by ring
    rw [e4] at hn4
    have := mul_le_mul_of_nonneg_left hp2 hAi0
    linarith
  have hde0 : 0 ≤ X.de C0 Cde := le_trans (by positivity) hLK
  have hcA : ((pairC mu i.val : ℤ) : ℝ) ≤ Ai := by nlinarith

  obtain ⟨hk1, -⟩ := hK i
  have hmax : max ((pairC mu i.val : ℤ) : ℝ) (Ai) = Ai := max_eq_right hcA
  rw [hmax] at hk1
  obtain ⟨-, -, -, -, -, -, t7, -⟩ := pair_top hP.1 i
  have h0 : ((0 : Fin X.m) : ℕ) = 0 := by simp
  have hrho : pairRho mu i.val ≤ pairC mu i.val := by
    unfold pairRho
    rw [finPos_eq (2 * segS X.TT j + 1) (2 * i.val + 2) (by omega)]
    exact t7 0 h0
  have hrhoR : ((pairRho mu i.val : ℤ) : ℝ) ≤ ((pairC mu i.val : ℤ) : ℝ) := by exact_mod_cast hrho
  have hpos : (0 : ℝ) ≤ 4 * ((Ai : ℝ) + X.m) / (X.p : ℝ) ^ 2 := by positivity
  have hO : ((pairO mu (clA C0 CE1 CE2 X j rz ry) i : ℤ) : ℝ) ≤ ((pairC mu i.val : ℤ) : ℝ) + X.La C0 * Ai / X.k := by
    rw [hkk]
    have : ((pairO mu (clA C0 CE1 CE2 X j rz ry) i - pairRho mu i.val : ℤ) : ℝ) =
        ((pairO mu (clA C0 CE1 CE2 X j rz ry) i : ℤ) : ℝ) - ((pairRho mu i.val : ℤ) : ℝ) := by push_cast; ring
    have key := hk1
    push_cast at key
    simp only [hAi] at key hpos hrhoR ⊢
    linarith
  refine ⟨?_, hO⟩
  have hLk : X.La C0 / X.k ≤ X.de C0 Cde / 2 := by
    have : X.La C0 / X.k ≤ 40 * X.N1 * X.La C0 / X.k / 2 := by
      rw [div_div, div_le_div_iff₀ hk (by positivity)]
      nlinarith [mul_nonneg (mul_nonneg (le_trans zero_le_one hLa1) hk.le) (by linarith : (0:ℝ) ≤ 40 * X.N1 - 2)]
    linarith
  have hfin : ((pairO mu (clA C0 CE1 CE2 X j rz ry) i : ℤ) : ℝ) ≤ Ai := by
    have e : X.La C0 * Ai / X.k = Ai * (X.La C0 / X.k) := by ring
    rw [e] at hO
    have := mul_le_mul_of_nonneg_left hLk hAi0
    nlinarith
  rw [hAi] at hfin
  have hfin' : ((pairO mu (clA C0 CE1 CE2 X j rz ry) i : ℤ) : ℝ) ≤ (((clA C0 CE1 CE2 X j rz ry i : ℕ) : ℤ) : ℝ) := by
    push_cast; exact hfin
  exact_mod_cast hfin'

theorem restPairU : RestPairU :=
  TransportedAlt.of_explicit (fun _ => 1) (fun _ _ => 1) (fun Cc _ CE1 CE2 _ => T2 CE1 CE2 Cc 1)
    fun _ _ _ _ _ _ _ _ _ _ hCc hC0 _ h1 h2 _ _ _ _ _ _ _ _ _ t1 t2 t3 t4 t5 =>
      pairU_at fun _ hD hI hc => std_of hCc hC0 h1 h2 le_rfl t1 t2 t3 t4 t5 hD hI hc

theorem kept_blocks_of_S_line (hS : RestPairS) : KeptBlocksBeyondThreshold := kept_blocks_of_three_lines restPairU hS restPairX

end Formalism.MainNotions.ColumnSystems.Pf
