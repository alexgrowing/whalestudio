import Formalism.HermitianCurvature.StatementSz

namespace Formalism.FourierDecayAlt.P.Sz1

open Finset Formalism.FourierDecayAlt.Sz

lemma half_eq (r : ℕ) : (2 * r + 2) * (2 * r + 2 - 1) / 2 = (r + 1) * (2 * r + 1) := by
  have h : (2 * r + 2) * (2 * r + 2 - 1) = 2 * ((r + 1) * (2 * r + 1)) := by
    have h1 : 2 * r + 2 - 1 = 2 * r + 1 := by omega
    rw [h1]; ring
  rw [h]; simp

lemma two_sum_Ioc (k p : ℕ) : 2 * ∑ M ∈ Ioc k (k + p), M = 2 * (p * k) + p * (p + 1) := by
  induction p with
  | zero => simp
  | succ p ih =>
    rw [← Nat.add_assoc, Finset.sum_Ioc_succ_top (by omega), mul_add, ih]; ring

lemma sum_Ioc_odd (k r : ℕ) :
    ∑ M ∈ Ioc k (k + (2 * r + 1)), M = (2 * r + 1) * k + (r + 1) * (2 * r + 1) := by
  have h := two_sum_Ioc k (2 * r + 1)
  have h2 : 2 * ((2 * r + 1) * k) + (2 * r + 1) * (2 * r + 1 + 1) =
      2 * ((2 * r + 1) * k + (r + 1) * (2 * r + 1)) := by ring
  rw [h2] at h
  exact Nat.eq_of_mul_eq_mul_left (by norm_num) h

lemma glCard_eq (p : ℕ) (q : ℝ) (hq : q ≠ 0) :
    glCard p q = q ^ (p * p) * ∏ i ∈ range p, (1 - (q ^ (i + 1))⁻¹) := by
  unfold glCard
  rw [← Finset.prod_range_reflect (fun i => (1 - (q ^ (i + 1))⁻¹)) p]
  have h : ∀ j ∈ range p, q ^ p - q ^ j = q ^ p * (1 - (q ^ (p - 1 - j + 1))⁻¹) := by
    intro j hj
    have hj' : j < p := Finset.mem_range.mp hj
    have e1 : p - 1 - j + 1 = p - j := by omega
    have e2 : q ^ p = q ^ j * q ^ (p - j) := by rw [← pow_add]; congr 1; omega
    have hne : q ^ (p - j) ≠ 0 := pow_ne_zero _ hq
    rw [e1, e2]; field_simp
  rw [Finset.prod_congr rfl h, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range,
    ← pow_mul]

lemma prod_split (k d : ℕ) (q : ℝ) :
    ∏ i ∈ range (k + d), (1 - (q ^ (i + 1))⁻¹) =
      (∏ i ∈ range k, (1 - (q ^ (i + 1))⁻¹)) * ∏ j ∈ Ioc k (k + d), (1 - (q ^ j)⁻¹) := by
  induction d with
  | zero => simp
  | succ d ih =>
    rw [← Nat.add_assoc, Finset.prod_range_succ, Finset.prod_Ioc_succ_top (by omega), ih, mul_assoc]

lemma prod_ne_zero (k : ℕ) (q : ℝ) (hq : 1 < q) :
    ∏ i ∈ range k, (1 - (q ^ (i + 1))⁻¹) ≠ 0 := by
  refine Finset.prod_ne_zero_iff.mpr ?_
  intro i _
  have h1 : 1 < q ^ (i + 1) := one_lt_pow₀ hq (by omega)
  have h2 : (q ^ (i + 1))⁻¹ < 1 := inv_lt_one_of_one_lt₀ h1
  linarith

lemma glCard_ne_zero (k : ℕ) (q : ℝ) (hq : 1 < q) : glCard k q ≠ 0 := by
  have hq0 : q ≠ 0 := by linarith
  rw [glCard_eq k q hq0]
  exact mul_ne_zero (pow_ne_zero _ hq0) (prod_ne_zero k q hq)

lemma colIdx_ne_zero (k : ℕ) (q : ℝ) (hq : 1 < q) : colIdx k q ≠ 0 := by
  have hq0 : q ≠ 0 := by linarith
  unfold colIdx
  exact div_ne_zero (glCard_ne_zero k q hq) (pow_ne_zero _ hq0)

lemma vol_chain {ι : Type} [Fintype ι] (S : SizeData ι) (hM : S.MassRatios) (d : ℕ)
    (hd : S.k + d ≤ S.n) :
    S.vol (S.k + d) =
      ((S.v / Real.pi) ^ (∑ M ∈ Ioc S.k (S.k + d), M) *
          ((∏ i ∈ Ico S.k (S.k + d), i.factorial : ℕ) : ℝ)) ^ S.f *
        (S.dF ^ (-(1 / 2 : ℝ))) ^ d * (∏ M ∈ Ioc S.k (S.k + d), S.Lv M) * S.vol S.k := by
  induction d with
  | zero => simp
  | succ d ih =>
    have h := hM (S.k + d + 1) (by omega) (by omega)
    rw [Nat.add_sub_cancel, ih (by omega)] at h
    rw [← Nat.add_assoc, h, Finset.sum_Ioc_succ_top (by omega), Finset.prod_Ioc_succ_top (by omega),
      Finset.prod_Ico_succ_top (by omega), pow_add, pow_succ]
    push_cast
    simp only [mul_pow]
    ring

lemma disc_pow (rd : ℝ) (hrd : 0 < rd) (f p : ℕ) :
    ((rd ^ f) ^ (-(1 / 2 : ℝ))) ^ p = (rd ^ (-((p : ℝ) / 2))) ^ f := by
  rw [← Real.rpow_natCast rd f, ← Real.rpow_mul hrd.le, ← Real.rpow_natCast _ p,
    ← Real.rpow_mul hrd.le, ← Real.rpow_natCast _ f, ← Real.rpow_mul hrd.le]
  congr 1; ring

end Formalism.FourierDecayAlt.P.Sz1

namespace Formalism.FourierDecayAlt.P

open Finset Formalism.FourierDecayAlt.Sz Formalism.FourierDecayAlt.P.Sz1

theorem sumRanks : Formalism.FourierDecayAlt.Sz.SumRanks := by
  intro k r m n hm hn
  subst hm
  have hn' : n = k + (2 * r + 1) := by omega
  subst hn'
  have h1 : 2 * r + 2 - 1 = 2 * r + 1 := by omega
  refine ⟨?_, ?_, ?_⟩
  · rw [half_eq, sum_Ioc_odd, h1]
  · rw [Nat.card_Ioc]; omega
  · rw [half_eq, h1]; ring

theorem levelExponent : Formalism.FourierDecayAlt.Sz.LevelExponent := by
  intro k r m n hm hn
  subst hm
  have hn' : n = k + 2 * r + 1 := by omega
  subst hn'
  rw [half_eq]
  unfold dimN
  constructor <;> ring

theorem indexRatio : Formalism.FourierDecayAlt.Sz.IndexRatio := by
  intro k r m n q hm hn hq
  have hq0 : q ≠ 0 := by linarith
  have hexp := (levelExponent k r m n hm hn).2
  have hn' : n = k + (2 * r + 1) := by omega
  have hn'' : k + 2 * r + 1 = n := by omega
  unfold rowIdx colIdx
  rw [hn'', glCard_eq n q hq0, glCard_eq k q hq0]
  have hsplit : ∏ i ∈ range n, (1 - (q ^ (i + 1))⁻¹) =
      (∏ i ∈ range k, (1 - (q ^ (i + 1))⁻¹)) * ∏ j ∈ Ioc k n, (1 - (q ^ j)⁻¹) := by
    rw [hn']; exact prod_split k (2 * r + 1) q
  have hG := prod_ne_zero k q hq
  have hpow : q ^ (n * n) = q ^ (k * k) * q ^ dimN k r * q ^ (k * m + m * (m - 1) / 2) := by
    rw [← pow_add, ← pow_add]; congr 1; rw [← sq, ← sq, hexp]
  rw [hsplit, hpow]
  have a1 : q ^ (k * k) ≠ 0 := pow_ne_zero _ hq0
  have a2 : q ^ dimN k r ≠ 0 := pow_ne_zero _ hq0
  have a3 : q ^ (k * (k - 1) / 2) ≠ 0 := pow_ne_zero _ hq0
  generalize (∏ i ∈ range k, (1 - (q ^ (i + 1))⁻¹)) = G at hG ⊢
  generalize (∏ j ∈ Ioc k n, (1 - (q ^ j)⁻¹)) = H
  field_simp

theorem factorialCancel : Formalism.FourierDecayAlt.Sz.FactorialCancel := by
  intro k n hkn
  unfold sfac
  rw [mul_comm]
  exact Finset.prod_range_mul_prod_Ico _ hkn

theorem volumeChain : Formalism.FourierDecayAlt.Sz.VolumeChain := by
  intro ι _ S hOk hM
  have hn : S.n = S.k + (2 * S.r + 1) := by unfold SizeData.n SizeData.m; omega
  have hm1 : S.m - 1 = 2 * S.r + 1 := by unfold SizeData.m; omega
  have hmR : (S.m : ℝ) - 1 = ((2 * S.r + 1 : ℕ) : ℝ) := by unfold SizeData.m; push_cast; ring
  have hsum := (sumRanks S.k S.r S.m S.n rfl rfl).1
  have h := vol_chain S hM (2 * S.r + 1) (by omega)
  rw [← hn, hsum] at h
  have hrd : 0 < S.rd := by unfold SizeData.rd; linarith [hOk.hv]
  have hdF : S.dF = S.rd ^ S.f := hOk.hdF
  have hka : S.v / Real.pi = S.ka⁻¹ := by unfold SizeData.ka; rw [inv_div]
  rw [h, hdF, disc_pow S.rd hrd, hka, inv_pow, hmR]
  simp only [mul_pow]
  ring

theorem massRatioFormula : Formalism.FourierDecayAlt.Sz.PropA := by
  intro ι _ S hOk hM hC
  have hvc := volumeChain ι S hOk hM
  have hkn : S.k ≤ S.n := by unfold SizeData.n SizeData.m; omega
  have hfac : ((∏ i ∈ Ico S.k S.n, i.factorial : ℕ) : ℝ) * (sfac S.k : ℝ) = (sfac S.n : ℝ) := by
    exact_mod_cast factorialCancel S.k S.n hkn
  have hg1 : (1 : ℝ) < S.g1 := by exact_mod_cast (lt_of_lt_of_le one_lt_two hOk.hg1)
  have hg2 : (1 : ℝ) < S.g2 := by exact_mod_cast (lt_of_lt_of_le one_lt_two hOk.hg2)
  have hT : (1 : ℝ) < S.T := by exact_mod_cast (lt_of_lt_of_le one_lt_two hOk.hT)
  have hi1 := indexRatio S.k S.r S.m S.n S.g1 rfl rfl hg1
  have hi2 := indexRatio S.k S.r S.m S.n S.g2 rfl rfl hg2
  have hc1 := colIdx_ne_zero S.k S.g1 hg1
  have hc2 := colIdx_ne_zero S.k S.g2 hg2
  rw [div_eq_iff hc1] at hi1
  rw [div_eq_iff hc2] at hi2
  have hsk : (sfac S.k : ℝ) ≠ 0 := by
    unfold sfac
    exact_mod_cast (Finset.prod_ne_zero_iff.mpr fun i _ => Nat.factorial_ne_zero i)
  have hTk : (1 : ℝ) < (S.T : ℝ) ^ S.k := one_lt_pow₀ hT (by have := hOk.hk; omega)
  have hTk0 : (S.T : ℝ) ^ S.k ≠ 0 := by linarith
  have hTk1 : (S.T : ℝ) ^ S.k - 1 ≠ 0 := by linarith
  have hVu : ∏ w, S.Vu w ≠ 0 := Finset.prod_ne_zero_iff.mpr fun w _ => (hOk.hVu w).ne'
  have hvol : S.vol S.k ≠ 0 := hOk.hvol.ne'
  have hdim : ∏ w, S.dimPi w = (∏ w, S.Vu w) / (sfac S.k : ℝ) ^ S.f := by
    unfold SizeData.dimPi SizeData.f
    rw [Finset.prod_div_distrib, Finset.prod_const, Finset.card_univ]
  have hprod : ∏ w, (S.TcritPow w / (S.T : ℝ) ^ S.k) =
      ((S.ka ^ ((S.m - 1) * S.k + S.m * (S.m - 1) / 2))⁻¹ * S.rd ^ (-(((S.m : ℝ) - 1) / 2)) *
        S.g ^ (S.k * S.m + S.m * (S.m - 1) / 2) * (sfac S.n : ℝ) / (S.T : ℝ) ^ S.k) ^ S.f *
        (∏ w, S.dsig w) / (∏ w, S.Vu w) := by
    have h : ∀ w ∈ (Finset.univ : Finset ι), S.TcritPow w / (S.T : ℝ) ^ S.k =
        ((S.ka ^ ((S.m - 1) * S.k + S.m * (S.m - 1) / 2))⁻¹ * S.rd ^ (-(((S.m : ℝ) - 1) / 2)) *
        S.g ^ (S.k * S.m + S.m * (S.m - 1) / 2) * (sfac S.n : ℝ) / (S.T : ℝ) ^ S.k) *
        S.dsig w / S.Vu w := by
      intro w _
      unfold SizeData.TcritPow Sz.TcritPow SizeData.VV
      ring
    rw [Finset.prod_congr rfl h, Finset.prod_div_distrib, Finset.prod_mul_distrib,
      Finset.prod_const, Finset.card_univ]
    rfl
  have hT1 : (1 - ((S.T : ℝ) ^ S.k)⁻¹) = ((S.T : ℝ) ^ S.k - 1) / (S.T : ℝ) ^ S.k := by
    field_simp
  rw [hprod, hC, hdim]
  unfold SizeData.Dstar SizeData.Ea SizeData.idxRow SizeData.idxCol SizeData.g
  rw [hvc, hi1, hi2, hT1, ← hfac]
  generalize (S.ka ^ ((S.m - 1) * S.k + S.m * (S.m - 1) / 2))⁻¹ = A
  generalize S.rd ^ (-(((S.m : ℝ) - 1) / 2)) = B
  generalize ((∏ i ∈ Ico S.k S.n, i.factorial : ℕ) : ℝ) = F
  generalize (∏ M ∈ Ioc S.k S.n, S.Lv M) = L
  generalize (∏ j ∈ Ioc S.k S.n, (1 - (((S.g1 : ℝ)) ^ j)⁻¹)) = P1
  generalize (∏ j ∈ Ioc S.k S.n, (1 - (((S.g2 : ℝ)) ^ j)⁻¹)) = P2
  generalize (∏ w, S.dsig w) = D
  generalize (∏ w, S.Vu w) = V at hVu ⊢
  generalize colIdx S.k (S.g1 : ℝ) = c1 at hc1 ⊢
  generalize colIdx S.k (S.g2 : ℝ) = c2 at hc2 ⊢
  generalize (sfac S.k : ℝ) = s at hsk ⊢
  generalize (S.T : ℝ) ^ S.k = t at hTk0 hTk1 ⊢
  generalize S.vol S.k = v0 at hvol ⊢
  generalize S.k * S.m + S.m * (S.m - 1) / 2 = e
  simp only [mul_pow, div_pow]
  field_simp

end Formalism.FourierDecayAlt.P
