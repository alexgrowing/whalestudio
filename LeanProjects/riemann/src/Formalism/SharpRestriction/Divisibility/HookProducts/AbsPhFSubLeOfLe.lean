import Formalism.LocalToGlobal.Divisibility.RecBridge
import Formalism.LocalRingCardinality.CoeNeZeroOfNotMem

noncomputable section

namespace Formalism.MainNotions.DIV.HookProducts.RBCompl3

open Formalism.BasicNotions

theorem phF_sub_le {y y' : ℝ} (hy : 0 < y) (hy' : 0 < y') :
    phF y - phF y' ≤ (y - y') * Real.log y := by
  have h1 : Real.log (y / y') ≤ y / y' - 1 := Real.log_le_sub_one_of_pos (div_pos hy hy')
  rw [Real.log_div hy.ne' hy'.ne'] at h1
  have h2 : y' * (Real.log y - Real.log y') ≤ y - y' := by
    have h3 := mul_le_mul_of_nonneg_left h1 hy'.le
    have h4 : y' * (y / y' - 1) = y - y' := by
      rw [mul_sub, mul_div_cancel₀ _ hy'.ne', mul_one]
    rw [h4] at h3
    exact h3
  have key : phF y - phF y' - (y - y') * Real.log y = -(y - y' - y' * (Real.log y - Real.log y')) := by
    unfold phF; ring
  linarith

theorem abs_phF_sub_le_of_le {y y' M : ℝ} (hy' : 1 ≤ y') (h : y' ≤ y) (hyM : y ≤ M) :
    |phF y - phF y'| ≤ (y - y') * Real.log M := by
  have hy : 0 < y := by linarith
  have hy'0 : 0 < y' := by linarith
  have hlow : phF y' - phF y ≤ (y' - y) * Real.log y' := phF_sub_le hy'0 hy
  have hneg : (y' - y) * Real.log y' ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg (by linarith) (Real.log_nonneg hy')
  have hup : phF y - phF y' ≤ (y - y') * Real.log y := phF_sub_le hy hy'0
  have hlog : Real.log y ≤ Real.log M := Real.log_le_log hy hyM
  have hup' : (y - y') * Real.log y ≤ (y - y') * Real.log M :=
    mul_le_mul_of_nonneg_left hlog (by linarith)
  rw [abs_of_nonneg (by linarith)]
  linarith

theorem abs_phF_sub_le {y y' M : ℝ} (hy : 1 ≤ y) (hy' : 1 ≤ y') (hyM : y ≤ M) (hy'M : y' ≤ M) :
    |phF y - phF y'| ≤ |y - y'| * Real.log M := by
  rcases le_total y' y with h | h
  · rw [abs_of_nonneg (sub_nonneg.mpr h)]
    exact abs_phF_sub_le_of_le hy' h hyM
  · rw [abs_sub_comm, abs_sub_comm y y', abs_of_nonneg (sub_nonneg.mpr h)]
    exact abs_phF_sub_le_of_le hy h hy'M

theorem nuRow_head' (D : D7) (u : D.what₂.Word) (j : ℕ) (τ : D.what₂.Tau) (r : ℕ) (hk : r < D.R.k) :
    DV.nuRow D u j τ r = (((D.hcW u τ).u ⟨r, hk⟩ : ℚ) : ℝ) + DV.wSz D j τ -
      (((D.R.N (j - 1) : ℝ) + D.R.N j - 1 - 2 * (r : ℝ)) / 2) := by
  unfold DV.nuRow DV.srcPar
  rw [dif_pos hk]

theorem nuRow_eq_of_not_mid (D : D7) (u u' : D.what₂.Word) (j : ℕ) (τ : D.what₂.Tau) (r : ℕ)
    (hr : ¬ (1 ≤ r ∧ r + 1 < D.R.k)) : DV.nuRow D u j τ r = DV.nuRow D u' j τ r := by
  have hs : DV.srcPar D u τ r = DV.srcPar D u' τ r := by
    unfold DV.srcPar
    by_cases hk : r < D.R.k
    · rw [dif_pos hk, dif_pos hk]
      rcases Nat.eq_zero_or_pos r with h0 | h0
      · subst h0
        rw [D.hcW_first u τ hk, D.hcW_first u' τ hk]
      · have hr' : r = D.R.k - 1 := by omega
        have hfin : (⟨r, hk⟩ : Fin D.R.k) = ⟨D.R.k - 1, by omega⟩ := Fin.ext hr'
        rw [hfin, D.hcW_last u τ (by omega), D.hcW_last u' τ (by omega)]
    · rw [dif_neg hk, dif_neg hk, D.hcW_e u τ, D.hcW_e u' τ]
  unfold DV.nuRow
  rw [hs]

theorem abs_nuRow_sub_le (D : D7) (L : SizeData₂ D) (u u' : D.what₂.Word) (j : ℕ) (τ : D.what₂.Tau) (r : ℕ)
    (hr : 1 ≤ r ∧ r + 1 < D.R.k) : |DV.nuRow D u j τ r - DV.nuRow D u' j τ r| ≤ L.Sc := by
  have hk : r < D.R.k := by omega
  rw [nuRow_head' D u j τ r hk, nuRow_head' D u' j τ r hk]
  have h1 := L.cloud_u u τ ⟨r, hk⟩ hr.1 hr.2
  have h2 := L.cloud_u u' τ ⟨r, hk⟩ hr.1 hr.2
  rw [abs_le]
  constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]

theorem nuRow_le (D : D7) (L : SizeData₂ D) (u : D.what₂.Word) (j : ℕ) (τ : D.what₂.Tau) (r : ℕ)
    (hr : 1 ≤ r ∧ r + 1 < D.R.k) : DV.nuRow D u j τ r ≤ L.Sc + DV.wSz D j τ := by
  have hk : r < D.R.k := by omega
  rw [nuRow_head' D u j τ r hk]
  have h1 := L.cloud_u u τ ⟨r, hk⟩ hr.1 hr.2
  have hN1 : r + 1 ≤ D.R.N (j - 1) := le_trans (by omega : r + 1 ≤ D.R.k) (Nat.le_add_right _ _)
  have hN2 : r + 1 ≤ D.R.N j := le_trans (by omega : r + 1 ≤ D.R.k) (Nat.le_add_right _ _)
  have hN1' : (r : ℝ) + 1 ≤ (D.R.N (j - 1) : ℝ) := by exact_mod_cast hN1
  have hN2' : (r : ℝ) + 1 ≤ (D.R.N j : ℝ) := by exact_mod_cast hN2
  have hs : 0 ≤ ((D.R.N (j - 1) : ℝ) + D.R.N j - 1 - 2 * (r : ℝ)) / 2 := by
    apply div_nonneg _ (by norm_num)
    linarith
  linarith [h1.2]

theorem abs_kerPlace_sub_le (D : D7) (L : SizeData₂ D) (u u' : D.what₂.Word) (i : ℕ) (hi : i < D.R.m)
    (τ : D.what₂.Tau) (M : ℝ) (hM1 : 1 ≤ M) (hM : L.Sc + DV.wSz D (i + 1) τ ≤ M) :
    |DV.kerPlace D L u (i + 1) τ - DV.kerPlace D L u' (i + 1) τ| ≤
      (D.R.k : ℝ) * (L.Sc * (Real.log M + |L.logOm|)) := by
  have hSc : 0 ≤ L.Sc := L.Sc_pos.le
  have hlM : 0 ≤ Real.log M := Real.log_nonneg hM1
  set B : ℝ := L.Sc * (Real.log M + |L.logOm|) with hB
  have hB0 : 0 ≤ B := mul_nonneg hSc (add_nonneg hlM (abs_nonneg _))
  unfold DV.kerPlace
  set S := Finset.range (D.R.N (i + 1 - 1)) with hS
  have e : ((∑ r ∈ S, phF (DV.nuRow D u (i + 1) τ r)) - (∑ r ∈ S, DV.nuRow D u (i + 1) τ r) * L.logOm) -
      ((∑ r ∈ S, phF (DV.nuRow D u' (i + 1) τ r)) - (∑ r ∈ S, DV.nuRow D u' (i + 1) τ r) * L.logOm) =
      ∑ r ∈ S, ((phF (DV.nuRow D u (i + 1) τ r) - phF (DV.nuRow D u' (i + 1) τ r)) -
        (DV.nuRow D u (i + 1) τ r - DV.nuRow D u' (i + 1) τ r) * L.logOm) := by
    simp only [Finset.sum_sub_distrib, ← Finset.sum_mul]
    ring
  rw [e]
  have key : ∀ r ∈ S, |(phF (DV.nuRow D u (i + 1) τ r) - phF (DV.nuRow D u' (i + 1) τ r)) -
      (DV.nuRow D u (i + 1) τ r - DV.nuRow D u' (i + 1) τ r) * L.logOm| ≤
      if (1 ≤ r ∧ r + 1 < D.R.k) then B else 0 := by
    intro r hr
    have hrN : r < D.R.N i := by
      rw [hS, Finset.mem_range] at hr
      simpa using hr
    by_cases hmid : 1 ≤ r ∧ r + 1 < D.R.k
    · rw [if_pos hmid]
      obtain ⟨n1, hn1, he1⟩ := nuRow_nat D u i hi τ r hrN
      obtain ⟨n2, hn2, he2⟩ := nuRow_nat D u' i hi τ r hrN
      have hy1 : (1 : ℝ) ≤ DV.nuRow D u (i + 1) τ r := by rw [he1]; exact_mod_cast hn1
      have hy2 : (1 : ℝ) ≤ DV.nuRow D u' (i + 1) τ r := by rw [he2]; exact_mod_cast hn2
      have hu1 := nuRow_le D L u (i + 1) τ r hmid
      have hu2 := nuRow_le D L u' (i + 1) τ r hmid
      have hd := abs_nuRow_sub_le D L u u' (i + 1) τ r hmid
      have hphi := abs_phF_sub_le (M := M) hy1 hy2 (by linarith) (by linarith)
      have hphi' : |phF (DV.nuRow D u (i + 1) τ r) - phF (DV.nuRow D u' (i + 1) τ r)| ≤ L.Sc * Real.log M :=
        le_trans hphi (mul_le_mul_of_nonneg_right hd hlM)
      have hlo : |(DV.nuRow D u (i + 1) τ r - DV.nuRow D u' (i + 1) τ r) * L.logOm| ≤ L.Sc * |L.logOm| := by
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_right hd (abs_nonneg _)
      have hA := abs_le.1 hphi'
      have hC := abs_le.1 hlo
      have hBe : B = L.Sc * Real.log M + L.Sc * |L.logOm| := by rw [hB]; ring
      rw [hBe, abs_le]
      constructor <;> linarith [hA.1, hA.2, hC.1, hC.2]
    · rw [if_neg hmid, nuRow_eq_of_not_mid D u u' (i + 1) τ r hmid]
      simp
  calc |∑ r ∈ S, ((phF (DV.nuRow D u (i + 1) τ r) - phF (DV.nuRow D u' (i + 1) τ r)) -
        (DV.nuRow D u (i + 1) τ r - DV.nuRow D u' (i + 1) τ r) * L.logOm)|
      ≤ ∑ r ∈ S, |(phF (DV.nuRow D u (i + 1) τ r) - phF (DV.nuRow D u' (i + 1) τ r)) -
        (DV.nuRow D u (i + 1) τ r - DV.nuRow D u' (i + 1) τ r) * L.logOm| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ r ∈ S, (if (1 ≤ r ∧ r + 1 < D.R.k) then B else 0) := Finset.sum_le_sum key
    _ = ((S.filter (fun r => 1 ≤ r ∧ r + 1 < D.R.k)).card : ℝ) * B := by
        rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul]
    _ ≤ (D.R.k : ℝ) * B := by
        apply mul_le_mul_of_nonneg_right _ hB0
        have hsub : S.filter (fun r => 1 ≤ r ∧ r + 1 < D.R.k) ⊆ Finset.range D.R.k := by
          intro r hr
          rw [Finset.mem_filter] at hr
          rw [Finset.mem_range]
          omega
        have := Finset.card_le_card hsub
        rw [Finset.card_range] at this
        exact_mod_cast this

end Formalism.MainNotions.DIV.HookProducts.RBCompl3

end
