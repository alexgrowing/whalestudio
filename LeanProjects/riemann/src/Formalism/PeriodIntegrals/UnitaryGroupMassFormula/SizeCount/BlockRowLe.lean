import Formalism.PeriodIntegrals.SzCt

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions.G
open scoped BigOperators

namespace PI.SzCt.W

theorem N_le_N (D : D7) (j : ℕ) : D.R.N (j - 1) ≤ D.R.N j := by
  unfold Formalism.BasicNotions.Ranks.N
  have : (j - 1) * (D.R.t + 1) ≤ j * (D.R.t + 1) := Nat.mul_le_mul_right _ (Nat.sub_le j 1)
  omega

theorem N_succ (D : D7) (j : ℕ) (hj : 1 ≤ j) : D.R.N j = D.R.N (j - 1) + (D.R.t + 1) := by
  unfold Formalism.BasicNotions.Ranks.N
  obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  ring

theorem shift_pos (D : D7) (j i : ℕ) (hi : i < D.R.N (j - 1)) :
    0 < (((D.R.N (j - 1) : ℝ) + D.R.N j - 1 - 2 * (i : ℝ)) / 2) := by
  have h1 : (D.R.N (j - 1) : ℝ) ≤ D.R.N j := by exact_mod_cast N_le_N D j
  have h2 : (i : ℝ) + 1 ≤ D.R.N (j - 1) := by exact_mod_cast hi
  apply div_pos _ two_pos
  linarith

theorem nuRow_le (D : D7) (u : D.what₂.Word) (j : ℕ) (τ : D.what₂.Tau) (i : ℕ)
    (hi : i < D.R.N (j - 1)) :
    DV.nuRow D u j τ i ≤ ((DV.srcPar D u τ i : ℚ) : ℝ) + DV.wSz D j τ := by
  have := shift_pos D j i hi
  unfold DV.nuRow
  linarith

theorem srcPar_lt (D : D7) (u : D.what₂.Word) (τ : D.what₂.Tau) (i : ℕ) (h : i < D.R.k) :
    DV.srcPar D u τ i = (D.hcW u τ).u ⟨i, h⟩ := by
  unfold DV.srcPar
  rw [dif_pos h]

theorem wSz_eq (D : D7) (j : ℕ) (τ : D.what₂.Tau) (hj : 1 ≤ j) (hm : j ≤ D.R.m) :
    DV.wSz D j τ = (((D.hc τ).e ⟨j - 1, by omega⟩ : ℚ) : ℝ) := by
  unfold DV.wSz
  rw [dif_pos ⟨hj, hm⟩]

theorem wSz_eq_wj (D : D7) (j : ℕ) (τ : D.what₂.Tau) (hj : 1 ≤ j) (hm : j ≤ D.R.m) :
    DV.wSz D j τ = wj D j τ := by
  rw [wSz_eq D j τ hj hm]
  unfold wj
  rw [dif_pos (by omega)]

theorem cloudRow_le (D : D7) (u : D.what₂.Word) (j : ℕ) (τ : D.what₂.Tau) (i : ℕ) (h : i < D.R.k) :
    DV.nuRow D u j τ i ≤ (((D.hcW u τ).u ⟨i, h⟩ : ℚ) : ℝ) + DV.wSz D j τ := by
  have hk : i < D.R.N (j - 1) := by
    unfold Formalism.BasicNotions.Ranks.N
    omega
  rw [← srcPar_lt D u τ i h]
  exact nuRow_le D u j τ i hk

theorem blockRow_le (D : D7) (L : SizeData₂ D) (u : D.what₂.Word) (j : ℕ) (τ : D.what₂.Tau) (i : ℕ)
    (hj : 1 ≤ j) (hm : j ≤ D.R.m) (hk : D.R.k ≤ i) (hi : i < D.R.N (j - 1)) :
    DV.nuRow D u j τ i ≤ 2 * L.etaSz := by

  obtain ⟨lo, hlo⟩ : ∃ lo : ℝ, ∀ j', 1 ≤ j' → j' ≤ D.R.m →
      lo ≤ wj D j' τ ∧ wj D j' τ ≤ lo + L.etaSz + 1 := by
    by_cases hth : (D.eTau τ : D.R.GG) ∈ D.host.thickPlaces
    · exact ⟨L.sc.b, fun j' h1 h2 => L.win_thick j' h1 h2 τ hth⟩
    by_cases htop : ∃ t0 : D.host.TT, (D.eTau τ : D.R.GG) = D.R.tau1 t0
    · obtain ⟨t0, ht0⟩ := htop
      refine ⟨(L.bT t0 : ℝ) + L.sc.b' / L.sc.x, fun j' h1 h2 => ?_⟩
      have hw := L.win_top j' h1 h2 τ t0 ht0
      exact ⟨hw.1, by linarith [hw.2]⟩
    · have hthin : D.host.IsThin (D.eTau τ : D.R.GG) := by
        refine ⟨(D.eTau τ).2, ?_, hth⟩
        intro hmem
        rw [Formalism.BasicNotions.Host.topPlaces, Finset.mem_image] at hmem
        obtain ⟨t0, ht0m, ht0⟩ := hmem
        exact htop ⟨⟨t0, ht0m⟩, ht0.symm⟩
      refine ⟨L.sc.w'' D.R.n, fun j' h1 h2 => ?_⟩
      have hw := L.win_thin j' h1 h2 τ hthin
      exact ⟨hw.1, by linarith [hw.2]⟩

  have ht1 : (1 : ℝ) ≤ D.R.t := by
    have := D.R.rank_add_five_le
    exact_mod_cast (by omega : 1 ≤ D.R.t)
  obtain ⟨b, hbdef⟩ : ∃ b, b = (i - D.R.k) / (D.R.t + 1) := ⟨_, rfl⟩
  obtain ⟨r, hrdef⟩ : ∃ r, r = (i - D.R.k) % (D.R.t + 1) := ⟨_, rfl⟩
  have hN1 : D.R.N (j - 1) = D.R.k + (j - 1) * (D.R.t + 1) := rfl
  have hN2 : D.R.N j = D.R.k + j * (D.R.t + 1) := rfl
  have hdec : i - D.R.k = b * (D.R.t + 1) + r := by
    rw [hbdef, hrdef]
    exact (Nat.div_add_mod' (i - D.R.k) (D.R.t + 1)).symm
  have hbj : b < j - 1 := by
    rw [hbdef, Nat.div_lt_iff_lt_mul (by omega)]
    rw [hN1] at hi
    omega
  have hbm : (i - D.R.k) / (D.R.t + 1) < D.R.m := by
    rw [← hbdef]
    omega
  have hwb : wj D (b + 1) τ = (((D.hc τ).e ⟨b, by omega⟩ : ℚ) : ℝ) := by
    unfold wj
    rw [dif_pos (by omega)]
    rfl
  have hEb : (((D.hc τ).e ⟨(i - D.R.k) / (D.R.t + 1), hbm⟩ : ℚ) : ℝ) = wj D (b + 1) τ := by
    rw [hwb]
    exact congrArg (fun x => (((D.hc τ).e x : ℚ) : ℝ)) (Fin.ext hbdef.symm)
  have hA := hlo j hj hm
  have hB := (hlo (b + 1) (by omega) (by omega)).1
  have hi' : i = D.R.k + b * (D.R.t + 1) + r := by omega
  have hir : (i : ℝ) = D.R.k + b * (D.R.t + 1) + r := by
    rw [hi']
    push_cast
    ring
  have hN1r : ((D.R.N (j - 1) : ℕ) : ℝ) = D.R.k + ((j : ℝ) - 1) * (D.R.t + 1) := by
    rw [hN1, Nat.cast_add, Nat.cast_mul, Nat.cast_sub hj]
    push_cast
    ring
  have hN2r : ((D.R.N j : ℕ) : ℝ) = D.R.k + (j : ℝ) * (D.R.t + 1) := by
    rw [hN2]
    push_cast
    ring
  have hbjr : (b : ℝ) + 1 ≤ (j : ℝ) - 1 := by
    have h2 : b + 2 ≤ j := by omega
    have h2' : ((b + 2 : ℕ) : ℝ) ≤ j := by exact_mod_cast h2
    push_cast at h2'
    linarith
  have hprod : ((D.R.t : ℝ) + 1) * 1 ≤ ((D.R.t : ℝ) + 1) * ((j : ℝ) - 1 - b) :=
    mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  unfold DV.nuRow DV.srcPar
  rw [dif_neg (by omega), dif_pos hbm, wSz_eq_wj D j τ hj hm, D.hcW_e]
  push_cast
  rw [hEb, ← hrdef, hN1r, hN2r, hir]
  nlinarith [hA.1, hA.2, hB]

end PI.SzCt.W
