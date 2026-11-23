import Formalism.HermitianCurvature.LatticeHerglotzBound

open Finset

noncomputable section

namespace Formalism.FourierDecayAlt.P.ChainAndRowSums

open Formalism.FourierDecayAlt.crystallineComparison

theorem cm_two {W : Type} (Wd : Finset W) (c : ℕ → W → W → ℝ) (k : ℕ) (w w'' : W) :
    chainMat Wd c (k + 2) w w'' = ∑ w' ∈ Wd, c (k + 2) w w' * chainMat Wd c (k + 1) w' w'' := by
  simp [chainMat]

theorem cm_one {W : Type} (Wd : Finset W) (c : ℕ → W → W → ℝ) : chainMat Wd c 1 = c 1 := by
  simp [chainMat]

theorem chainSum_ok : ChainSum := by
  intro W X Wd s c caa Nd N0 T hs h1 htr hfin
  have key : ∀ n, 1 ≤ n → n ≤ s - 1 → ∀ w ∈ Wd, ∀ t,
      Nd n w t ≤ ∑ w'' ∈ Wd, chainMat Wd c n w w'' * N0 w'' := by
    intro n
    induction n with
    | zero => intro h; omega
    | succ m ih =>
      intro _ hns w hw t
      rcases Nat.eq_zero_or_pos m with rfl | hm
      · simpa [cm_one] using h1 w hw t
      · obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
        have ih' := ih (by omega) (by omega)
        have h := htr (k + 1 + 1) (by omega) hns
          (fun w' => ∑ w'' ∈ Wd, chainMat Wd c (k + 1) w' w'' * N0 w'')
          (by intro w' hw' t'; simpa using ih' w' hw' t') w hw t
        calc Nd (k + 1 + 1) w t
            ≤ ∑ w' ∈ Wd, c (k + 1 + 1) w w' *
                ∑ w'' ∈ Wd, chainMat Wd c (k + 1) w' w'' * N0 w'' := h
          _ = ∑ w'' ∈ Wd, chainMat Wd c (k + 1 + 1) w w'' * N0 w'' := by
            rw [show k + 1 + 1 = k + 2 from rfl]
            simp only [cm_two, Finset.mul_sum, Finset.sum_mul]
            rw [Finset.sum_comm]
            refine Finset.sum_congr rfl (fun _ _ => Finset.sum_congr rfl (fun _ _ => by ring))
  intro w hw
  have h := hfin (fun w' => ∑ w'' ∈ Wd, chainMat Wd c (s - 1) w' w'' * N0 w'')
    (fun w' hw' t => key (s - 1) (by omega) le_rfl w' hw' t) w hw
  calc T w ≤ ∑ w' ∈ Wd, caa w w' * ∑ w'' ∈ Wd, chainMat Wd c (s - 1) w' w'' * N0 w'' := h
    _ = ∑ w'' ∈ Wd, coMat Wd c caa s w w'' * N0 w'' := by
      simp only [coMat, Finset.mul_sum, Finset.sum_mul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl (fun _ _ => Finset.sum_congr rfl (fun _ _ => by ring))

theorem cm_nonneg {W : Type} (Wd : Finset W) (c : ℕ → W → W → ℝ) (hc : ∀ n w w', 0 ≤ c n w w') :
    ∀ n w w', 0 ≤ chainMat Wd c n w w' := by
  have : ∀ n, (∀ w w', 0 ≤ chainMat Wd c n w w') ∧ (∀ w w', 0 ≤ chainMat Wd c (n + 1) w w') := by
    intro n
    induction n with
    | zero =>
      refine ⟨fun w w' => ?_, fun w w' => ?_⟩
      · simp only [chainMat]; split_ifs <;> norm_num
      · rw [cm_one]; exact hc 1 w w'
    | succ m ih =>
      refine ⟨ih.2, fun w w' => ?_⟩
      rw [cm_two]
      exact Finset.sum_nonneg (fun x _ => mul_nonneg (hc _ _ _) (ih.2 _ _))
  exact fun n => (this n).1

theorem rowSums_ok : RowSums := by
  intro W Wd s c caa M Maa hs hc hcaa hM hMaa
  have row : ∀ n, 1 ≤ n → n < s → ∀ w ∈ Wd,
      ∑ w'' ∈ Wd, chainMat Wd c n w w'' = ∏ k ∈ Ico 1 (n + 1), M k := by
    intro n
    induction n with
    | zero => intro h; omega
    | succ m ih =>
      intro _ hns w hw
      rcases Nat.eq_zero_or_pos m with rfl | hm
      · simp [cm_one, hM 1 le_rfl hns w hw]
      · obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
        rw [show k + 1 + 1 = k + 2 from rfl]
        simp only [cm_two]
        rw [Finset.sum_comm]
        simp only [← Finset.mul_sum]
        rw [Finset.sum_congr rfl (fun w' hw' => by rw [ih (by omega) (by omega) w' hw'])]
        rw [← Finset.sum_mul, hM (k + 2) (by omega) hns w hw,
          Finset.prod_Ico_succ_top (a := 1) (b := k + 2) (by omega), mul_comm]
  have P := fun w hw => row (s - 1) (by omega) (by omega) w hw
  have hs1 : s - 1 + 1 = s := by omega
  rw [hs1] at P
  have rsum : ∀ w ∈ Wd, ∑ w'' ∈ Wd, coMat Wd c caa s w w'' = Maa * ∏ n ∈ Ico 1 s, M n := by
    intro w hw
    simp only [coMat]
    rw [Finset.sum_comm]
    simp only [← Finset.mul_sum]
    rw [Finset.sum_congr rfl (fun w' hw' => by rw [P w' hw']), ← Finset.sum_mul, hMaa w hw]
  intro w hw
  refine ⟨rsum w hw, fun hpos => ⟨fun a => ?_, fun a ha => by simp [ha], ?_⟩⟩
  · dsimp only
    split_ifs
    · exact div_nonneg (Finset.sum_nonneg (fun x _ => mul_nonneg (hcaa _ _)
        (cm_nonneg Wd c hc _ _ _))) hpos.le
    · exact le_rfl
  · rw [Finset.sum_congr rfl (fun a ha => if_pos ha), ← Finset.sum_div, rsum w hw]
    exact div_self hpos.ne'

theorem sizesProduct_ok : SizesProduct := by
  intro f s Maa C₄ A B M vol hs hC hA0 hAC hB0 hBC hvol hMaa0 hMaaA hM
  have hC0 : 0 ≤ C₄ := by linarith
  have hprodv : 0 ≤ ∏ n ∈ Ico 1 s, vol n := Finset.prod_nonneg (fun n _ => hvol n)
  have h1 : ∏ n ∈ Ico 1 s, M n ≤ ∏ n ∈ Ico 1 s, (B ^ f * vol n) :=
    Finset.prod_le_prod (fun n hn => (hM n hn).1) (fun n hn => (hM n hn).2)
  have h2 : ∏ n ∈ Ico 1 s, (B ^ f * vol n) ≤ ∏ n ∈ Ico 1 s, (C₄ ^ f * vol n) :=
    Finset.prod_le_prod (fun n _ => mul_nonneg (pow_nonneg hB0 _) (hvol n))
      (fun n _ => mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hB0 hBC f) (hvol n))
  have h3 : A ^ f ≤ C₄ ^ f := pow_le_pow_left₀ hA0 hAC f
  have hMp : 0 ≤ ∏ n ∈ Ico 1 s, M n := Finset.prod_nonneg (fun n hn => (hM n hn).1)
  calc Maa * ∏ n ∈ Ico 1 s, M n ≤ C₄ ^ f * ∏ n ∈ Ico 1 s, (C₄ ^ f * vol n) := by
        apply mul_le_mul (hMaaA.trans h3) (h1.trans h2) hMp (pow_nonneg hC0 _)
    _ = C₄ ^ (f * s) * ∏ n ∈ Ico 1 s, vol n := by
        rw [Finset.prod_mul_distrib, Finset.prod_const, Nat.card_Ico, ← mul_assoc, ← pow_mul,
          ← pow_add]
        congr 2
        rcases s with _ | s
        · omega
        · simp [Nat.mul_succ]; ring

end Formalism.FourierDecayAlt.P.ChainAndRowSums

theorem Formalism.FourierDecayAlt.P.chain_sum_identity : Formalism.FourierDecayAlt.crystallineComparison.ChainSum := Formalism.FourierDecayAlt.P.ChainAndRowSums.chainSum_ok
theorem Formalism.FourierDecayAlt.P.row_sums_identity : Formalism.FourierDecayAlt.crystallineComparison.RowSums := Formalism.FourierDecayAlt.P.ChainAndRowSums.rowSums_ok
theorem Formalism.FourierDecayAlt.P.sizes_product_identity : Formalism.FourierDecayAlt.crystallineComparison.SizesProduct :=
  Formalism.FourierDecayAlt.P.ChainAndRowSums.sizesProduct_ok
