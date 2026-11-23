import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.LevelLossDegreeBounds
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockDegreeGapBound
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemHeightOneIdealIffAdditiveValuationPos
open Formalism.BasicNotions Formalism.BasicNotions.DV Formalism.MainNotions Formalism.MainNotions.G NumberField GlobalTheory.IndefiniteRowSideFullHecke.LevelLossDegreeBounds

namespace GlobalTheory.FockDegreeFine

open Classical GlobalTheory.FockDegreeGap

variable {D : D7} {L : SizeData₂ D}

noncomputable def topConst (D : D7) (c : ℝ) (τ : D.what₂.Tau) : ℝ :=
  ∑ t : D.host.TT, if (D.eTau τ : D.R.GG) = D.R.tau1 t then c else 0

theorem topConst_top (c : ℝ) {τ : D.what₂.Tau} {t : D.host.TT}
    (h : (D.eTau τ : D.R.GG) = D.R.tau1 t) : topConst D c τ = c := by
  unfold topConst
  rw [Finset.sum_eq_single t, if_pos h]
  · intro s _ hs
    exact if_neg fun h' => hs (Subtype.ext (tau1_injective (h'.symm.trans h)))
  · simp

theorem topConst_nonneg {c : ℝ} (hc : 0 ≤ c) (τ : D.what₂.Tau) : 0 ≤ topConst D c τ := by
  unfold topConst
  refine Finset.sum_nonneg fun t _ => ?_
  split_ifs
  · exact hc
  · exact le_rfl

theorem sum_topConst (c : ℝ) : ∑ τ, topConst D c τ = (D.host.TT.card : ℝ) * c := by
  unfold topConst
  rw [Finset.sum_comm]
  have : ∀ t ∈ (Finset.univ : Finset D.host.TT),
      (∑ τ : D.what₂.Tau, if (D.eTau τ : D.R.GG) = D.R.tau1 t then c else 0) = c := by
    intro t _
    rw [Finset.sum_eq_single (D.eTau.symm ⟨D.R.tau1 t, (Formalism.HC.Frame.mem_Psi_iff _).2 rfl⟩)]
    · simp
    · intro τ _ hτ
      refine if_neg fun h' => hτ ?_
      rw [Equiv.eq_symm_apply]
      exact Subtype.ext h'
    · simp
  rw [Finset.sum_congr rfl this]
  simp

noncomputable def offWt (D : D7) (j : ℕ) (τ : D.what₂.Tau) : ℝ :=
  if τ ∉ topsOf D.host D.eTau then wj D j τ else 0

theorem mem_topsOf (τ : D.what₂.Tau) :
    τ ∈ topsOf D.host D.eTau ↔ (D.eTau τ : D.R.GG) ∈ D.host.topPlaces := by
  unfold topsOf
  simp

theorem sum_offWt (j : ℕ) : ∑ τ, offWt D j τ = sizeOffTops D j := by
  unfold offWt sizeOffTops
  rw [Finset.sum_filter]

theorem end_rows (P : ParameterChoice' D L) (u : D.what₂.Word) (i : ℕ) (hi : i < D.R.m) (τ : D.what₂.Tau) :
    |nuRow D u (i + 1) τ 0 + nuRow D u (i + 1) τ (D.R.k - 1) - wj D (i + 1) τ -
        (topWt L τ + offWt D (i + 1) τ)| ≤
      4 * L.Sc + 2 * D.R.N D.R.m + 1 + L.etaSz + topConst D (L.sc.b' / L.sc.x) τ := by
  have hk : 5 ≤ D.R.k := by have := D.R.m_add_three_le_k; have := D.R.two_le_m; omega
  have hk0 : 0 < D.R.k := by omega
  have hS := L.Sc_pos
  have he := L.etaSz_pos
  have hNm : (0 : ℝ) ≤ D.R.N D.R.m := Nat.cast_nonneg _
  have hc : 0 ≤ L.sc.b' / L.sc.x :=
    div_nonneg (GlobalTheory.HCEntries.b'_pos L).le (by linarith [L.sc.one_lt_alt])
  obtain ⟨a1, a2⟩ := head_row u i hi τ 0 hk0
  obtain ⟨b1, b2⟩ := head_row u i hi τ (D.R.k - 1) (by omega)
  rw [D.hcW_first u τ hk0] at a1 a2
  rw [D.hcW_last u τ hk0] at b1 b2
  rw [abs_le]
  unfold offWt
  by_cases ha : (D.eTau τ : D.R.GG) ∈ D.host.topPlaces
  · obtain ⟨t, ht⟩ := GlobalTheory.HCEntries.exists_top ha
    rw [topWt_top L ht, topConst_top _ ht, if_neg (not_not.2 ((mem_topsOf τ).2 ha))]
    rw [(L.top_u τ t hk0 ht).1] at a1 a2
    rw [(L.top_u τ t hk0 ht).2] at b1 b2
    obtain ⟨c1, c2⟩ := L.win_top (i + 1) (by omega) hi τ t ht
    constructor <;> linarith
  · rw [topWt_off L ha, if_pos (fun h => ha ((mem_topsOf τ).1 h))]
    rw [P.uk_extreme τ (by omega) ha] at b1 b2
    have h0 := topConst_nonneg hc τ
    have h1 := P.cloud_place_bound τ (by omega) ha
    have h2 := L.cloud_v τ ⟨0, by omega⟩
    have h3 : (((D.hc τ).v ⟨0, by omega⟩ : ℚ) : ℝ) < (((D.hc τ).u ⟨0, hk0⟩ : ℚ) : ℝ) := by
      exact_mod_cast (D.hc τ).u_gt_v ⟨0, by omega⟩
    have h4 := L.cloud_v τ ⟨D.R.k - 2, by omega⟩
    push_cast at h1 b1 b2
    constructor <;> linarith [h2.1, h2.2, h4.1, h4.2]

theorem nuAbs_place_fine (P : ParameterChoice' D L) (u : D.what₂.Word) (i : ℕ) (hi : i < D.R.m) (τ : D.what₂.Tau) :
    |nuAbs D u (i + 1) τ - ((D.R.k : ℝ) - 1) * wj D (i + 1) τ - (topWt L τ + offWt D (i + 1) τ)| ≤
      D.R.k * (L.Sc + D.R.N D.R.m) + D.R.m * ((D.R.t : ℝ) + 1) * (2 * L.etaSz) +
        (4 * L.Sc + 2 * D.R.N D.R.m + 1 + L.etaSz + topConst D (L.sc.b' / L.sc.x) τ) := by
  obtain ⟨n, hn⟩ : ∃ n, D.R.k = n + 2 := ⟨D.R.k - 2, by have := D.R.m_add_three_le_k; omega⟩
  have hN : D.R.N (i + 1 - 1) = n + 1 + 1 + i * (D.R.t + 1) := by unfold Ranks.N; rw [hn]; rfl
  have hS := L.Sc_pos
  have he := L.etaSz_pos
  have hNm : (0 : ℝ) ≤ D.R.N D.R.m := Nat.cast_nonneg _
  have hkn : (D.R.k : ℝ) = n + 2 := by exact_mod_cast hn
  have s0 := abs_le.1 (end_rows P u i hi τ)
  rw [show D.R.k - 1 = n + 1 by omega] at s0
  unfold nuAbs
  rw [hN, Finset.sum_range_add, Finset.sum_range_succ, Finset.sum_range_succ']
  have hmid : ∀ r < n, |nuRow D u (i + 1) τ (r + 1) - wj D (i + 1) τ| ≤ L.Sc + D.R.N D.R.m := by
    intro r hr
    obtain ⟨a1, a2⟩ := head_row u i hi τ (r + 1) (by omega)
    obtain ⟨b1, b2⟩ := L.cloud_u u τ ⟨r + 1, by omega⟩ (by show 1 ≤ r + 1; omega) (by show r + 1 + 1 < D.R.k; omega)
    rw [abs_le]
    constructor <;> linarith
  have s1 := abs_le.1 (abs_sum_range_sub _ n _ _ hmid)
  have s2 := abs_le.1 (abs_sum_range_sub (fun r => nuRow D u (i + 1) τ (n + 1 + 1 + r)) (i * (D.R.t + 1)) 0 _
    (fun r hr => block_row L u i hi τ _ (by omega) (by unfold Ranks.N; omega)))
  have hi' : (i : ℝ) ≤ D.R.m := by exact_mod_cast hi.le
  have s8 : (i : ℝ) * ((D.R.t : ℝ) + 1) * (2 * L.etaSz) ≤ D.R.m * ((D.R.t : ℝ) + 1) * (2 * L.etaSz) := by gcongr
  push_cast at s2
  rw [mul_zero] at s2
  rw [hkn, abs_le]
  constructor <;> linarith [s0.1, s0.2, s1.1, s1.2, s2.1, s2.2]

theorem arith (k m t N S η : ℝ) (hm : 1 ≤ m) (hk : 1 ≤ k) (hkm : k + m ≤ N) (ht : 1 ≤ t) (hS : 0 ≤ S) (hη : 0 ≤ η) :
    k * (S + N) + m * (t + 1) * (2 * η) + (4 * S + 2 * N + 1 + η) + (k * (S + 2 * N) + 2 * m * (η + 2 * N)) ≤
      20 * (k * S + N ^ 2 + m * t * η) := by
  have h1 : S ≤ k * S := le_mul_of_one_le_left hS hk
  have h2 : k * N ≤ N * N := mul_le_mul_of_nonneg_right (by linarith) (by linarith)
  have h3 : m * N ≤ N * N := mul_le_mul_of_nonneg_right (by linarith) (by linarith)
  have h4 : N ≤ N * N := le_mul_of_one_le_left (by linarith) (by linarith)
  have h5 : η ≤ m * η := le_mul_of_one_le_left hη hm
  have h6 : m * η ≤ t * (m * η) := le_mul_of_one_le_left (by linarith) ht
  nlinarith

theorem degree_fine : ∀ {D : D7} (L : SizeData₂ D), SizesAt L → ParameterChoice' D L → KapDef D → 2 ≤ L.sc.x → ∀ (u : D.what₂.Word), ∀ j ∈ SizeData₂.lifts D, |degPi D u j - (fockDeg D j : ℝ) - (topSum L + sizeOffTops D j)| ≤ 20 * degErr L := by
  intro D L h P hK hx u j hj
  obtain ⟨j1, j2⟩ := Finset.mem_Icc.1 hj
  obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
  have hc : 0 ≤ L.sc.b' / L.sc.x :=
    div_nonneg (GlobalTheory.HCEntries.b'_pos L).le (by linarith [L.sc.one_lt_alt])
  have hm : (1 : ℝ) ≤ D.R.m := by exact_mod_cast (by have := D.R.two_le_m; omega : 1 ≤ D.R.m)
  have har := arith D.R.k D.R.m D.R.t (D.R.N D.R.m) L.Sc L.etaSz hm (GlobalTheory.HCEntries.one_le_k D) (ranks_le D).1
    L.t_win.1 L.Sc_pos.le L.etaSz_pos.le
  unfold degPi fockDeg topSum degErr Nm
  rw [← sum_topWt, ← sum_offWt, Int.cast_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib,
    ← Finset.sum_sub_distrib]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  refine (Finset.sum_le_sum (g := fun τ => 20 * ((D.R.k : ℝ) * L.Sc + (D.R.N D.R.m : ℝ) ^ 2 +
    (D.R.m : ℝ) * (D.R.t : ℝ) * L.etaSz) + topConst D (L.sc.b' / L.sc.x) τ) fun τ _ => ?_).trans ?_
  · obtain ⟨w0, -⟩ := GlobalTheory.HCEntries.wj_bounds h hx (i + 1) j1 j2 τ
    have a := abs_le.1 (nuAbs_place_fine P u i j2 τ)
    have b := abs_le.1 (letters_place L hK i j2 τ w0)
    rw [abs_le]
    constructor <;> linarith [a.1, a.2, b.1, b.2]
  · rw [Finset.sum_add_distrib, sum_topConst, Finset.sum_const, Finset.card_univ, D.what₂.card_Tau, nsmul_eq_mul,
      mul_div_assoc]
    have : 0 ≤ (D.host.TT.card : ℝ) * (L.sc.b' / L.sc.x) := mul_nonneg (Nat.cast_nonneg _) hc
    linarith

end GlobalTheory.FockDegreeFine
