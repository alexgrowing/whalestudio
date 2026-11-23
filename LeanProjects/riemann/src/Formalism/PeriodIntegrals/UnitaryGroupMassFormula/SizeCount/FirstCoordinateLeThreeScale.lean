import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SizeCount.Development
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SizeCount.BlockRowLe

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions.G
open scoped BigOperators

namespace PI.SzCt.UnitaryGroupMassFormula

open PI.SzCt.W

theorem five_le_k (D : D7) : 5 ≤ D.R.k := by
  have h1 := D.R.m_add_three_le_k
  have h2 := D.R.two_le_m
  omega

theorem cloudU_le (D : D7) (L : SizeData₂ D) (u : D.what₂.Word) (τ : D.what₂.Tau) (i : ℕ) (h : i < D.R.k)
    (h1 : 1 ≤ i) : (((D.hcW u τ).u ⟨i, h⟩ : ℚ) : ℝ) ≤ L.Sc := by
  by_cases hi : i + 1 < D.R.k
  · exact (L.cloud_u u τ ⟨i, h⟩ h1 hi).2
  · have hk := five_le_k D
    have hik : i = D.R.k - 1 := by omega
    have hgt := (D.hc τ).v_gt_u ⟨D.R.k - 2, by omega⟩
    have hv := (L.cloud_v τ ⟨D.R.k - 2, by omega⟩).2
    have hlast := D.hcW_last u τ (by omega)
    have e1 : (⟨i, h⟩ : Fin D.R.k) = ⟨D.R.k - 1, by omega⟩ := Fin.ext hik
    have hgt' : (D.hc τ).u ⟨D.R.k - 1, by omega⟩ < (D.hc τ).v ⟨D.R.k - 2, by omega⟩ := by
      have e2 : (⟨D.R.k - 1, by omega⟩ : Fin D.R.k) = ⟨D.R.k - 2 + 1, by omega⟩ :=
        Fin.ext (show D.R.k - 1 = D.R.k - 2 + 1 by omega)
      rw [e2]
      exact hgt
    have hgtR : (((D.hc τ).u ⟨D.R.k - 1, by omega⟩ : ℚ) : ℝ) <
        (((D.hc τ).v ⟨D.R.k - 2, by omega⟩ : ℚ) : ℝ) := by exact_mod_cast hgt'
    rw [e1, hlast]
    linarith

private lemma wSz_eq_wj' (D : D7) (j : ℕ) (τ : D.what₂.Tau) (hj1 : 1 ≤ j) (hj2 : j ≤ D.R.m) :
    DV.wSz D j τ = wj D j τ := by
  unfold DV.wSz wj
  rw [dif_pos ⟨hj1, hj2⟩, dif_pos (by omega : j - 1 < D.R.m)]

private lemma exists_wj_mem_Icc_add_etaSz (D : D7) (L : SizeData₂ D) (τ : D.what₂.Tau) :
    ∃ lo : ℝ, ∀ j, 1 ≤ j → j ≤ D.R.m → lo ≤ wj D j τ ∧ wj D j τ ≤ lo + L.etaSz + 1 := by
  have hPsi : (D.eTau τ : D.R.GG) ∈ D.R.Psi := (D.eTau τ).2
  by_cases htop : (D.eTau τ : D.R.GG) ∈ D.host.topPlaces
  · unfold Formalism.BasicNotions.Host.topPlaces at htop
    rw [Finset.mem_image] at htop
    obtain ⟨t, ht, hteq⟩ := htop
    refine ⟨(L.bT ⟨t, ht⟩ : ℝ) + L.sc.b' / L.sc.x, fun j hj1 hj2 => ?_⟩
    have hw := L.win_top j hj1 hj2 τ ⟨t, ht⟩ hteq.symm
    constructor <;> linarith [hw.1, hw.2]
  · by_cases hthick : (D.eTau τ : D.R.GG) ∈ D.host.thickPlaces
    · refine ⟨L.sc.b, fun j hj1 hj2 => ?_⟩
      have hw := L.win_thick j hj1 hj2 τ hthick
      constructor <;> linarith [hw.1, hw.2]
    · have hthin : D.host.IsThin (D.eTau τ : D.R.GG) := ⟨hPsi, htop, hthick⟩
      refine ⟨L.sc.w'' D.R.n, fun j hj1 hj2 => ?_⟩
      have hw := L.win_thin j hj1 hj2 τ hthin
      constructor <;> linarith [hw.1, hw.2]

private lemma hcW_e_cast_eq_wj_succ (D : D7) (u : D.what₂.Word) (τ : D.what₂.Tau) (q : ℕ) (hq : q < D.R.m) :
    (((D.hcW u τ).e ⟨q, hq⟩ : ℚ) : ℝ) = wj D (q + 1) τ := by
  unfold wj
  rw [dif_pos (by omega : q + 1 - 1 < D.R.m), D.hcW_e u τ]
  have e : (⟨q + 1 - 1, by omega⟩ : Fin D.R.m) = ⟨q, hq⟩ := Fin.ext (show q + 1 - 1 = q by omega)
  rw [e]

theorem blocks_le (D : D7) (L : SizeData₂ D) (u : D.what₂.Word) (j : ℕ) (τ : D.what₂.Tau)
    (hj : 1 ≤ j) (hm : j ≤ D.R.m) :
    ∑ i ∈ Finset.Ico D.R.k (D.R.N (j - 1)), DV.nuRow D u j τ i ≤
      2 * (D.R.m : ℝ) * ((D.R.t : ℝ) + 1) * L.etaSz := by
  obtain ⟨lo, hlo⟩ := exists_wj_mem_Icc_add_etaSz D L τ
  have hη : 0 ≤ L.etaSz := L.etaSz_pos.le
  have ht0 : (0 : ℝ) ≤ (D.R.t : ℝ) := Nat.cast_nonneg _
  have hN1 : D.R.N (j - 1) = D.R.k + (j - 1) * (D.R.t + 1) := rfl
  have hterm : ∀ i ∈ Finset.Ico D.R.k (D.R.N (j - 1)), DV.nuRow D u j τ i ≤ L.etaSz := by
    intro i hi
    rw [Finset.mem_Ico] at hi
    obtain ⟨hi1, hi2⟩ := hi
    have ht1 : 0 < D.R.t + 1 := Nat.succ_pos _
    have hlt : i - D.R.k < (j - 1) * (D.R.t + 1) := by rw [hN1] at hi2; omega
    have hq_lt : (i - D.R.k) / (D.R.t + 1) < j - 1 := (Nat.div_lt_iff_lt_mul ht1).2 hlt
    have hqm : (i - D.R.k) / (D.R.t + 1) < D.R.m := lt_of_lt_of_le hq_lt (by omega)
    have hdm := Nat.div_add_mod (i - D.R.k) (D.R.t + 1)
    have hnk : ¬ i < D.R.k := by omega
    have he := hcW_e_cast_eq_wj_succ D u τ _ hqm
    have hnat : ∀ q : ℕ, q < j - 1 → q + 1 ≤ D.R.m ∧ q + 2 ≤ j := fun q h1 => by omega
    obtain ⟨hq1, hq2⟩ := hnat _ hq_lt
    obtain ⟨hlo0, -⟩ := hlo ((i - D.R.k) / (D.R.t + 1) + 1) (Nat.succ_pos _) hq1
    obtain ⟨-, hhi⟩ := hlo j hj hm
    have hw := wSz_eq_wj' D j τ hj hm
    have hiR : (i : ℝ) = (D.R.k : ℝ) + ((D.R.t : ℝ) + 1) * (((i - D.R.k) / (D.R.t + 1) : ℕ) : ℝ) +
        (((i - D.R.k) % (D.R.t + 1) : ℕ) : ℝ) := by
      have hsplit : ∀ A : ℕ, A = i - D.R.k → i = D.R.k + A := fun A hA => by omega
      have h' := hsplit _ hdm
      conv_lhs => rw [h']
      push_cast
      ring
    have hN1R : (D.R.N (j - 1) : ℝ) = (D.R.k : ℝ) + ((j : ℝ) - 1) * ((D.R.t : ℝ) + 1) := by
      rw [hN1]
      push_cast [Nat.cast_sub hj]
      ring
    have hN2R : (D.R.N j : ℝ) = (D.R.k : ℝ) + (j : ℝ) * ((D.R.t : ℝ) + 1) := by
      show ((D.R.k + j * (D.R.t + 1) : ℕ) : ℝ) = _
      push_cast
      ring
    have hqj : ((((i - D.R.k) / (D.R.t + 1) : ℕ) : ℝ)) + 2 ≤ (j : ℝ) := by
      exact_mod_cast hq2
    have hprod : 0 ≤ ((D.R.t : ℝ) + 1) * ((j : ℝ) - (((i - D.R.k) / (D.R.t + 1) : ℕ) : ℝ) - 2) :=
      mul_nonneg (by linarith) (by linarith)
    unfold DV.nuRow DV.srcPar
    rw [dif_neg hnk, dif_pos hqm, hw, hN1R, hN2R, hiR]
    push_cast
    nlinarith
  calc ∑ i ∈ Finset.Ico D.R.k (D.R.N (j - 1)), DV.nuRow D u j τ i
      ≤ ∑ _i ∈ Finset.Ico D.R.k (D.R.N (j - 1)), L.etaSz := Finset.sum_le_sum hterm
    _ = ((D.R.N (j - 1) - D.R.k : ℕ) : ℝ) * L.etaSz := by
        rw [Finset.sum_const, Nat.card_Ico, nsmul_eq_mul]
    _ ≤ 2 * (D.R.m : ℝ) * ((D.R.t : ℝ) + 1) * L.etaSz := by
        have hN : D.R.N (j - 1) - D.R.k = (j - 1) * (D.R.t + 1) := by
          rw [hN1]
          exact Nat.add_sub_cancel_left _ _
        rw [hN, Nat.cast_mul, Nat.cast_sub hj]
        push_cast
        have hjm : (j : ℝ) ≤ (D.R.m : ℝ) := by exact_mod_cast hm
        have hj1 : (1 : ℝ) ≤ (j : ℝ) := by exact_mod_cast hj
        have hp : 0 ≤ (2 * (D.R.m : ℝ) - ((j : ℝ) - 1)) * ((D.R.t : ℝ) + 1) * L.etaSz :=
          mul_nonneg (mul_nonneg (by linarith) (by linarith)) hη
        nlinarith

theorem nuAbs_split (D : D7) (u : D.what₂.Word) (j : ℕ) (τ : D.what₂.Tau) :
    nuAbs D u j τ = (∑ i ∈ Finset.range (D.R.k - 1), DV.nuRow D u j τ (i + 1)) + DV.nuRow D u j τ 0 +
      ∑ i ∈ Finset.Ico D.R.k (D.R.N (j - 1)), DV.nuRow D u j τ i := by
  have hk := five_le_k D
  have hN : D.R.k ≤ D.R.N (j - 1) := by
    unfold Formalism.BasicNotions.Ranks.N
    exact Nat.le_add_right _ _
  have hr : ∑ i ∈ Finset.range D.R.k, DV.nuRow D u j τ i =
      (∑ i ∈ Finset.range (D.R.k - 1), DV.nuRow D u j τ (i + 1)) + DV.nuRow D u j τ 0 := by
    have h := Finset.sum_range_succ' (fun i => DV.nuRow D u j τ i) (D.R.k - 1)
    rw [Nat.sub_add_cancel (by omega : 1 ≤ D.R.k)] at h
    exact h
  unfold nuAbs
  rw [← Finset.sum_range_add_sum_Ico _ hN, hr]

private lemma nuRow_le_Sc_add_wSz (D : D7) (L : SizeData₂ D) (u : D.what₂.Word) (j : ℕ) (τ : D.what₂.Tau) (i : ℕ)
    (h1 : 1 ≤ i) (hi : i < D.R.k) : DV.nuRow D u j τ i ≤ L.Sc + DV.wSz D j τ := by
  have hu := cloudU_le D L u τ i hi h1
  have hN1 : (D.R.k : ℝ) ≤ (D.R.N (j - 1) : ℝ) := by
    unfold Formalism.BasicNotions.Ranks.N
    exact_mod_cast Nat.le_add_right _ _
  have hN2 : (D.R.k : ℝ) ≤ (D.R.N j : ℝ) := by
    unfold Formalism.BasicNotions.Ranks.N
    exact_mod_cast Nat.le_add_right _ _
  have hik : (i : ℝ) + 1 ≤ (D.R.k : ℝ) := by exact_mod_cast hi
  unfold DV.nuRow DV.srcPar
  rw [dif_pos hi]
  linarith

theorem cloudRows_le (D : D7) (L : SizeData₂ D) (u : D.what₂.Word) (j : ℕ) (τ : D.what₂.Tau) :
    ∑ i ∈ Finset.range (D.R.k - 1), DV.nuRow D u j τ (i + 1) ≤
      ((D.R.k : ℝ) - 1) * (L.Sc + DV.wSz D j τ) := by
  have hk := five_le_k D
  calc ∑ i ∈ Finset.range (D.R.k - 1), DV.nuRow D u j τ (i + 1)
      ≤ ∑ _i ∈ Finset.range (D.R.k - 1), (L.Sc + DV.wSz D j τ) := by
        apply Finset.sum_le_sum
        intro i hi
        rw [Finset.mem_range] at hi
        exact nuRow_le_Sc_add_wSz D L u j τ (i + 1) (by omega) (by omega)
    _ = ((D.R.k : ℝ) - 1) * (L.Sc + DV.wSz D j τ) := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, Nat.cast_sub (by omega : 1 ≤ D.R.k)]
        push_cast
        ring

theorem rowA : RowA := by
  intro D L j hj u τ
  simp only [SizeData₂.lifts, Finset.mem_Icc] at hj
  obtain ⟨hj1, hj2⟩ := hj
  have hk := five_le_k D
  have hw := wSz_eq_wj' D j τ hj1 hj2
  have hsplit := nuAbs_split D u j τ
  have hcl := cloudRows_le D L u j τ
  have hbl := blocks_le D L u j τ hj1 hj2
  have hr1 := nuRow_le_Sc_add_wSz D L u j τ 1 le_rfl (by omega)
  rw [hw] at hcl hr1
  have e : ((D.R.k : ℝ) - 1) * (L.Sc + wj D j τ) + (L.Sc + wj D j τ) =
      (D.R.k : ℝ) * (L.Sc + wj D j τ) := by ring
  rw [hsplit]
  linarith

theorem first_coordinate_le_three_scale (D : D7) (L : SizeData₂ D) (P : ParameterChoice' D L) (u : D.what₂.Word) (τ : D.what₂.Tau)
    (hτ : (D.eTau τ : D.R.GG) ∉ D.host.topPlaces) :
    (((D.hcW u τ).u ⟨0, by have := five_le_k D; omega⟩ : ℚ) : ℝ) ≤ 3 * L.Sc := by
  have hk := five_le_k D
  have hfirst := D.hcW_first u τ (by omega)
  have h2 := P.cloud_place_bound τ (by omega) hτ
  have hv := (L.cloud_v τ ⟨0, by omega⟩).2
  rw [hfirst]
  push_cast at h2
  linarith

theorem rowC : RowC := by
  intro D L P j hj u τ hτ
  simp only [SizeData₂.lifts, Finset.mem_Icc] at hj
  obtain ⟨hj1, hj2⟩ := hj
  have hk := five_le_k D
  have hu := first_coordinate_le_three_scale D L P u τ hτ
  have hw := wSz_eq_wj' D j τ hj1 hj2
  have hN1 : (D.R.k : ℝ) ≤ (D.R.N (j - 1) : ℝ) := by
    unfold Formalism.BasicNotions.Ranks.N
    exact_mod_cast Nat.le_add_right _ _
  have hN2 : (D.R.k : ℝ) ≤ (D.R.N j : ℝ) := by
    unfold Formalism.BasicNotions.Ranks.N
    exact_mod_cast Nat.le_add_right _ _
  have hk5 : (5 : ℝ) ≤ (D.R.k : ℝ) := by exact_mod_cast hk
  unfold DV.nuRow DV.srcPar
  rw [dif_pos (by omega : 0 < D.R.k), hw]
  push_cast
  linarith

theorem rowB : RowB := by
  intro D L P j hj u τ hτ
  have hC := rowC D L P j hj u τ hτ
  simp only [SizeData₂.lifts, Finset.mem_Icc] at hj
  obtain ⟨hj1, hj2⟩ := hj
  have hw := wSz_eq_wj' D j τ hj1 hj2
  have hsplit := nuAbs_split D u j τ
  have hcl := cloudRows_le D L u j τ
  have hbl := blocks_le D L u j τ hj1 hj2
  rw [hw] at hcl
  have e : ((D.R.k : ℝ) - 1) * (L.Sc + wj D j τ) + (3 * L.Sc + wj D j τ) =
      ((D.R.k : ℝ) + 2) * L.Sc + (D.R.k : ℝ) * wj D j τ := by ring
  rw [hsplit]
  linarith

end PI.SzCt.UnitaryGroupMassFormula
