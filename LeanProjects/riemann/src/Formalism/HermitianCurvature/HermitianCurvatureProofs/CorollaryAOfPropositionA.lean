import Formalism.HermitianCurvature.StatementSz
import Formalism.HermitianCurvature.HermitianCurvatureProofs.MassRatioFormula

namespace Formalism.FourierDecayAlt.P.Sz2

open Finset Formalism.FourierDecayAlt.Sz

lemma term_le (M N : ℕ) (hM : 3 ≤ M) (hN : 1 ≤ N) :
    1 / ((N : ℝ) + 1) ^ M ≤
      4 / 2 ^ M * (1 / ((N : ℝ) * (N + 1)) - 1 / (((N : ℝ) + 1) * (N + 2))) := by
  obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le hM
  have hN' : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have h1 : 4 / (2 : ℝ) ^ (3 + t) * (1 / ((N : ℝ) * (N + 1)) - 1 / (((N : ℝ) + 1) * (N + 2)))
      = 1 / (2 ^ t * ((N : ℝ) * (N + 1) * (N + 2))) := by
    rw [pow_add]
    field_simp
    ring
  rw [h1]
  apply one_div_le_one_div_of_le (by positivity)
  rw [pow_add, mul_comm]
  have h2 : (2 : ℝ) ^ t ≤ ((N : ℝ) + 1) ^ t := pow_le_pow_left₀ (by norm_num) (by linarith) t
  have h3 : (N : ℝ) * (N + 1) * (N + 2) ≤ ((N : ℝ) + 1) ^ 3 := by nlinarith
  exact mul_le_mul h3 h2 (by positivity) (by positivity)

lemma partial_le (M : ℕ) (hM : 3 ≤ M) (n : ℕ) :
    ∑ i ∈ range (n + 1), 1 / ((i : ℝ) + 1) ^ M ≤
      1 + 2 / 2 ^ M - 4 / 2 ^ M * (1 / (((n : ℝ) + 1) * (n + 2))) := by
  induction n with
  | zero =>
    simp
    have : (0 : ℝ) < 2 ^ M := by positivity
    apply le_of_eq
    field_simp
    ring
  | succ n ih =>
    rw [sum_range_succ]
    have h := term_le M (n + 1) hM (by omega)
    push_cast at h ⊢
    have e1 : (n : ℝ) + 1 + 1 + 1 = n + 1 + 2 := by ring
    have e2 : (n : ℝ) + 1 + 1 = n + 2 := by ring
    rw [e2] at h ⊢
    have e3 : (n : ℝ) + 1 + 2 = n + 2 + 1 := by ring
    rw [e3] at h ⊢
    rw [mul_sub] at h
    linarith

lemma zeta_sub_one_le (M : ℕ) (hM : 3 ≤ M) :
    ∑' j : ℕ, 1 / ((j : ℝ) + 1) ^ M ≤ 1 + 2 / 2 ^ M := by
  apply Real.tsum_le_of_sum_range_le
  · intro n; positivity
  · intro n
    cases n with
    | zero => simp; positivity
    | succ n =>
      have h := partial_le M hM n
      have : (0 : ℝ) ≤ 4 / 2 ^ M * (1 / (((n : ℝ) + 1) * (n + 2))) := by positivity
      linarith

theorem zetaTail : ZetaTail := by
  intro M hM
  have h := zeta_sub_one_le M hM
  have h0 : (0 : ℝ) ≤ ∑' j : ℕ, 1 / ((j : ℝ) + 1) ^ M := tsum_nonneg (fun j => by positivity)
  rcases h0.eq_or_lt with h0 | h0
  · rw [← h0]; simp only [Real.log_zero]; positivity
  · have := Real.log_le_sub_one_of_pos h0
    linarith

lemma abs_log_one_sub_le {x : ℝ} (h0 : 0 ≤ x) (h1 : x ≤ 1 / 2) :
    |Real.log (1 - x)| ≤ 2 * x := by
  have hpos : 0 < 1 - x := by linarith
  have hle : Real.log (1 - x) ≤ 0 := Real.log_nonpos hpos.le (by linarith)
  rw [abs_of_nonpos hle]
  have h2 := Real.log_le_sub_one_of_pos (inv_pos.mpr hpos)
  rw [Real.log_inv] at h2
  have h3 : (1 - x)⁻¹ ≤ 1 + 2 * x := by
    rw [inv_le_iff_one_le_mul₀ hpos]
    nlinarith
  linarith

lemma geom_eq (k d : ℕ) :
    ∑ j ∈ Ioc k (k + d), 1 / (2 : ℝ) ^ j = 1 / 2 ^ k - 1 / 2 ^ (k + d) := by
  induction d with
  | zero => simp
  | succ d ih =>
    rw [← add_assoc, Finset.sum_Ioc_succ_top (by omega), ih, pow_succ (2 : ℝ) (k + d)]
    field_simp
    ring

lemma geom_le (k n : ℕ) : ∑ j ∈ Ioc k n, 1 / (2 : ℝ) ^ j ≤ 1 / 2 ^ k := by
  rcases le_total k n with h | h
  · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
    rw [geom_eq]
    have : (0 : ℝ) < 1 / 2 ^ (k + d) := by positivity
    linarith
  · rw [Finset.Ioc_eq_empty (by omega)]
    simp

lemma inv_pow_bounds (q j : ℕ) (hq : 2 ≤ q) (hj : 1 ≤ j) :
    0 ≤ ((q : ℝ) ^ j)⁻¹ ∧ ((q : ℝ) ^ j)⁻¹ ≤ 1 / 2 ^ j ∧ (1 : ℝ) / 2 ^ j ≤ 1 / 2 := by
  have hq' : (2 : ℝ) ≤ q := by exact_mod_cast hq
  refine ⟨by positivity, ?_, ?_⟩
  · rw [← one_div]
    exact one_div_le_one_div_of_le (by positivity) (pow_le_pow_left₀ (by norm_num) hq' j)
  · apply one_div_le_one_div_of_le (by norm_num)
    calc (2 : ℝ) = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ j := pow_le_pow_right₀ (by norm_num) hj

lemma prod_one_sub (q : ℕ) (hq : 2 ≤ q) (k n : ℕ) :
    0 < ∏ j ∈ Ioc k n, (1 - ((q : ℝ) ^ j)⁻¹) ∧
      |Real.log (∏ j ∈ Ioc k n, (1 - ((q : ℝ) ^ j)⁻¹))| ≤ 2 / 2 ^ k := by
  have hpos : ∀ j ∈ Ioc k n, 0 < 1 - ((q : ℝ) ^ j)⁻¹ := by
    intro j hj
    have hj1 : 1 ≤ j := by have := (mem_Ioc.mp hj).1; omega
    obtain ⟨_, h2, h3⟩ := inv_pow_bounds q j hq hj1
    linarith
  refine ⟨prod_pos hpos, ?_⟩
  rw [Real.log_prod (fun j hj => (hpos j hj).ne')]
  calc |∑ j ∈ Ioc k n, Real.log (1 - ((q : ℝ) ^ j)⁻¹)|
      ≤ ∑ j ∈ Ioc k n, |Real.log (1 - ((q : ℝ) ^ j)⁻¹)| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ j ∈ Ioc k n, 2 * (1 / (2 : ℝ) ^ j) := by
        apply sum_le_sum
        intro j hj
        have hj1 : 1 ≤ j := by have := (mem_Ioc.mp hj).1; omega
        obtain ⟨h1, h2, h3⟩ := inv_pow_bounds q j hq hj1
        have := abs_log_one_sub_le h1 (h2.trans h3)
        linarith
    _ = 2 * ∑ j ∈ Ioc k n, 1 / (2 : ℝ) ^ j := by rw [mul_sum]
    _ ≤ 2 * (1 / 2 ^ k) := by
        have := geom_le k n
        linarith
    _ = 2 / 2 ^ k := by ring

theorem eaSize : EaSize := by
  intro ι _ S hOk hL hk _ _
  have hA : ∀ M ∈ Ioc S.k S.n, 0 < S.Lv M := fun M hM =>
    (hL M (mem_Ioc.mp hM).1 (mem_Ioc.mp hM).2).1
  have hApos : 0 < ∏ M ∈ Ioc S.k S.n, S.Lv M := prod_pos hA
  obtain ⟨hB1, hB1'⟩ := prod_one_sub S.g1 hOk.hg1 S.k S.n
  obtain ⟨hB2, hB2'⟩ := prod_one_sub S.g2 hOk.hg2 S.k S.n
  obtain ⟨t1, t2, t3⟩ := inv_pow_bounds S.T S.k hOk.hT hOk.hk
  have hT : 0 < 1 - ((S.T : ℝ) ^ S.k)⁻¹ := by linarith
  have hT' : |Real.log (1 - ((S.T : ℝ) ^ S.k)⁻¹)| ≤ 2 / 2 ^ S.k := by
    have := abs_log_one_sub_le t1 (t2.trans t3)
    calc _ ≤ 2 * ((S.T : ℝ) ^ S.k)⁻¹ := this
      _ ≤ 2 * (1 / 2 ^ S.k) := by linarith
      _ = 2 / 2 ^ S.k := by ring
  have hf : (0 : ℝ) ≤ S.f := Nat.cast_nonneg _
  have hA' : |Real.log (∏ M ∈ Ioc S.k S.n, S.Lv M)| ≤ (S.f : ℝ) * (2 / 2 ^ S.k) := by
    rw [Real.log_prod (fun j hj => (hA j hj).ne')]
    calc |∑ M ∈ Ioc S.k S.n, Real.log (S.Lv M)|
        ≤ ∑ M ∈ Ioc S.k S.n, |Real.log (S.Lv M)| := abs_sum_le_sum_abs _ _
      _ ≤ ∑ M ∈ Ioc S.k S.n, (S.f : ℝ) * (2 * (1 / (2 : ℝ) ^ M)) := by
          apply sum_le_sum
          intro M hM
          have hM1 := (mem_Ioc.mp hM).1
          have h1 := (hL M hM1 (mem_Ioc.mp hM).2).2
          have h2 := zetaTail M (by omega)
          calc _ ≤ _ := h1
            _ ≤ (S.f : ℝ) * (2 / 2 ^ M) := mul_le_mul_of_nonneg_left h2 hf
            _ = _ := by ring
      _ = (S.f : ℝ) * (2 * ∑ M ∈ Ioc S.k S.n, 1 / (2 : ℝ) ^ M) := by rw [mul_sum, mul_sum]
      _ ≤ (S.f : ℝ) * (2 * (1 / 2 ^ S.k)) := by
          have := geom_le S.k S.n
          apply mul_le_mul_of_nonneg_left _ hf
          linarith
      _ = _ := by ring
  have hEa : 0 < S.Ea := by
    unfold SizeData.Ea
    positivity
  refine ⟨hEa, ?_⟩
  have hlog : Real.log S.Ea = Real.log (∏ M ∈ Ioc S.k S.n, S.Lv M) +
      ((S.f : ℝ) * Real.log (∏ j ∈ Ioc S.k S.n, (1 - ((S.g1 : ℝ) ^ j)⁻¹)) +
        (S.f : ℝ) * Real.log (∏ j ∈ Ioc S.k S.n, (1 - ((S.g2 : ℝ) ^ j)⁻¹))) -
      (S.f : ℝ) * Real.log (1 - ((S.T : ℝ) ^ S.k)⁻¹) := by
    unfold SizeData.Ea
    rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
      Real.log_mul (by positivity) (by positivity), Real.log_inv, Real.log_pow, Real.log_pow,
      Real.log_pow]
    ring
  rw [hlog]
  have a1 := abs_le.mp hA'
  have a2 := abs_le.mp hB1'
  have a3 := abs_le.mp hB2'
  have a4 := abs_le.mp hT'
  have b2l := mul_le_mul_of_nonneg_left a2.1 hf
  have b2r := mul_le_mul_of_nonneg_left a2.2 hf
  have b3l := mul_le_mul_of_nonneg_left a3.1 hf
  have b3r := mul_le_mul_of_nonneg_left a3.2 hf
  have b4l := mul_le_mul_of_nonneg_left a4.1 hf
  have b4r := mul_le_mul_of_nonneg_left a4.2 hf
  have e8 : (S.f : ℝ) * (8 / 2 ^ S.k) = 4 * ((S.f : ℝ) * (2 / 2 ^ S.k)) := by ring
  rw [e8, abs_le]
  constructor <;> linarith

lemma ratio_bounds {G2 C0 R du : ℝ} (hG20 : 0 < G2) (hC0 : 1 ≤ C0) (hdu : du ≠ 0)
    (c1 : G2⁻¹ * (R * du) * C0⁻¹ ≤ du) (c2 : du ≤ G2⁻¹ * (R * du) * C0) :
    G2 / C0 ≤ R ∧ R ≤ G2 * C0 := by
  have hC00 : 0 < C0 := by linarith
  have c1' : (R / (G2 * C0)) * du ≤ 1 * du := by
    calc _ = G2⁻¹ * (R * du) * C0⁻¹ := by field_simp
      _ ≤ _ := by rw [one_mul]; exact c1
  have c2' : 1 * du ≤ (R / (G2 / C0)) * du := by
    calc _ = du := one_mul _
      _ ≤ _ := c2
      _ = _ := by field_simp
  have hle : G2 / C0 ≤ G2 * C0 := by
    rw [div_le_iff₀ hC00]
    have h1 : 1 ≤ C0 * C0 := by nlinarith
    have h2 := mul_le_mul_of_nonneg_left h1 hG20.le
    linarith
  have p1 : 0 < G2 * C0 := by positivity
  have p2 : 0 < G2 / C0 := by positivity
  rcases lt_or_gt_of_ne hdu with hneg | hpos
  · have d1 : 1 ≤ R / (G2 * C0) := by
      by_contra hcon
      have hcon' : R / (G2 * C0) - 1 < 0 := by linarith [not_le.mp hcon]
      have := mul_pos_of_neg_of_neg hneg hcon'
      linarith
    have d2 : R / (G2 / C0) ≤ 1 := by
      by_contra hcon
      have hcon' : 1 - R / (G2 / C0) < 0 := by linarith [not_le.mp hcon]
      have := mul_pos_of_neg_of_neg hneg hcon'
      linarith
    rw [le_div_iff₀ p1] at d1
    rw [div_le_iff₀ p2] at d2
    constructor <;> linarith
  · have d1 : R / (G2 * C0) ≤ 1 := le_of_mul_le_mul_right c1' hpos
    have d2 : 1 ≤ R / (G2 / C0) := le_of_mul_le_mul_right c2' hpos
    rw [div_le_iff₀ p1] at d1
    rw [le_div_iff₀ p2] at d2
    constructor <;> linarith

lemma root_bounds {P Ea C0 X : ℝ} {k : ℕ} (hP0 : 0 < P) (hk1 : 1 ≤ k) (hC0 : 1 ≤ C0)
    (hX0 : 0 ≤ X) (hX8 : 8 * X ≤ k) (hEa12 : 1 / 2 ≤ Ea) (hEa2 : Ea ≤ 2)
    (hlo : Real.exp (2 * X) / C0 ≤ Ea * P ^ k) (hhi : Ea * P ^ k ≤ Real.exp (2 * X) * C0) :
    (2 * C0) ^ (-(1 / (k : ℝ))) ≤ P ∧
      P ≤ (2 * C0) ^ (1 / (k : ℝ)) * Real.exp (1 / 4) ∧
      (2 * C0) ^ (1 / (k : ℝ)) * Real.exp (1 / 4) ≤ 2 * C0 * Real.exp (1 / 4) := by
  have hkne : k ≠ 0 := by omega
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk1
  have hkR1 : (1 : ℝ) ≤ k := by exact_mod_cast hk1
  have hC00 : 0 < C0 := by linarith
  have hPk0 : 0 < P ^ k := pow_pos hP0 _
  have hG20 : 0 < Real.exp (2 * X) := Real.exp_pos _
  have hG21 : 1 ≤ Real.exp (2 * X) := Real.one_le_exp (by linarith)
  have h2C : 0 < 2 * C0 := by linarith
  have hlow : (2 * C0)⁻¹ ≤ P ^ k := by
    have h1 : 1 / C0 ≤ Ea * P ^ k :=
      le_trans (div_le_div_of_nonneg_right hG21 hC00.le) hlo
    have h2 : Ea * P ^ k ≤ 2 * P ^ k := mul_le_mul_of_nonneg_right hEa2 hPk0.le
    have h3 : (2 * C0)⁻¹ = 1 / C0 / 2 := by field_simp
    rw [h3]
    linarith
  have hup : P ^ k ≤ 2 * C0 * Real.exp (2 * X) := by
    have h2 : 1 / 2 * P ^ k ≤ Ea * P ^ k := mul_le_mul_of_nonneg_right hEa12 hPk0.le
    linarith
  have hPr : (P ^ k) ^ ((k : ℝ)⁻¹) = P := Real.pow_rpow_inv_natCast hP0.le hkne
  have hkinv : 0 ≤ (k : ℝ)⁻¹ := by positivity
  refine ⟨?_, ?_, ?_⟩
  · rw [Real.rpow_neg h2C.le, ← Real.inv_rpow h2C.le, one_div]
    calc ((2 * C0)⁻¹) ^ ((k : ℝ)⁻¹) ≤ (P ^ k) ^ ((k : ℝ)⁻¹) :=
          Real.rpow_le_rpow (by positivity) hlow hkinv
      _ = P := hPr
  · rw [one_div]
    calc P = (P ^ k) ^ ((k : ℝ)⁻¹) := hPr.symm
      _ ≤ (2 * C0 * Real.exp (2 * X)) ^ ((k : ℝ)⁻¹) :=
          Real.rpow_le_rpow hPk0.le hup hkinv
      _ = (2 * C0) ^ ((k : ℝ)⁻¹) * Real.exp (2 * X) ^ ((k : ℝ)⁻¹) :=
          Real.mul_rpow h2C.le hG20.le
      _ ≤ (2 * C0) ^ ((k : ℝ)⁻¹) * Real.exp (1 / 4) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          rw [← Real.exp_mul]
          apply Real.exp_le_exp.mpr
          rw [← div_eq_mul_inv, div_le_iff₀ hkR]
          linarith
  · apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
    calc (2 * C0) ^ (1 / (k : ℝ)) ≤ (2 * C0) ^ (1 : ℝ) := by
          apply Real.rpow_le_rpow_of_exponent_le (by linarith)
          rw [div_le_iff₀ hkR]; linarith
      _ = 2 * C0 := Real.rpow_one _

lemma tcritPow_pos {ι : Type} [Fintype ι] (S : SizeData ι) (hOk : S.Ok)
    (hds : ∀ w, 0 < S.dsig w) (w : ι) : 0 < S.TcritPow w := by
  have hv := hOk.hv
  have hg10 : (0 : ℝ) < S.g1 := by
    have := hOk.hg1
    exact_mod_cast (by omega : 0 < S.g1)
  have hg20 : (0 : ℝ) < S.g2 := by
    have := hOk.hg2
    exact_mod_cast (by omega : 0 < S.g2)
  have h1 : 0 < S.ka := by unfold SizeData.ka; have := Real.pi_pos; positivity
  have h2 : 0 < S.rd := by unfold SizeData.rd; positivity
  have h3 : 0 < S.g := by unfold SizeData.g; positivity
  have h4 : 0 < S.VV w := by
    unfold SizeData.VV
    have h5 : 0 < sfac S.n := by
      unfold sfac
      exact Finset.prod_pos (fun i _ => Nat.factorial_pos i)
    have h6 : (0 : ℝ) < (sfac S.n : ℝ) := by exact_mod_cast h5
    exact mul_pos (hds w) h6
  have h5 := hOk.hVu w
  unfold SizeData.TcritPow Sz.TcritPow
  positivity

theorem corA_of_propA (hPA : PropA) : CorA := by
  intro ι _ S C0 CG C' L hOk hMR hLB hCC hds hk hg1 hg2 hC0 hCG hL hC' hkb hf2 hCh
  obtain ⟨hEa, hEa'⟩ := eaSize ι S hOk hLB hk hg1 hg2
  have hPA' := hPA ι S hOk hMR hCC
  obtain ⟨X, hX⟩ : ∃ X : ℝ, X = CG * (S.m : ℝ) ^ 5 * S.f * L := ⟨_, rfl⟩
  rw [← hX] at hCh
  have hk1 : 1 ≤ S.k := hOk.hk
  have hkne : S.k ≠ 0 := by omega
  have hT0 : (0 : ℝ) < S.T := by
    have := hOk.hT
    exact_mod_cast (by omega : 0 < S.T)
  have hmfL : 0 ≤ (S.m : ℝ) ^ 5 * S.f * L := by positivity
  have hX0 : 0 ≤ X := by
    have := mul_nonneg hCG hmfL
    rw [hX]
    linarith
  have hX8 : 8 * X ≤ S.k := by
    have h1 : 8 * CG * ((S.m : ℝ) ^ 5 * S.f * L) ≤ C' * ((S.m : ℝ) ^ 5 * S.f * L) :=
      mul_le_mul_of_nonneg_right hC' hmfL
    rw [hX]
    linarith
  have hTP : ∀ w, 0 < S.TcritPow w := tcritPow_pos S hOk hds
  have hTc0 : ∀ w, 0 < S.Tcrit w := by
    intro w
    exact Real.rpow_pos_of_pos (hTP w) _
  have hTc : ∀ w, S.Tcrit w ^ S.k = S.TcritPow w := by
    intro w
    have : S.Tcrit w = (S.TcritPow w) ^ ((S.k : ℝ)⁻¹) := by
      unfold SizeData.Tcrit Sz.Tcrit SizeData.TcritPow
      rw [one_div]
    rw [this, Real.rpow_inv_natCast_pow (hTP w).le hkne]
  obtain ⟨P, hP⟩ : ∃ P : ℝ, P = ∏ w, (S.Tcrit w / S.T) := ⟨_, rfl⟩
  rw [← hP]
  have hP0 : 0 < P := by
    rw [hP]
    exact Finset.prod_pos (fun w _ => div_pos (hTc0 w) hT0)
  have hPk : P ^ S.k = ∏ w, (S.TcritPow w / (S.T : ℝ) ^ S.k) := by
    rw [hP, ← Finset.prod_pow]
    apply Finset.prod_congr rfl
    intro w _
    rw [div_pow, hTc]
  rw [← hPk] at hPA'
  obtain ⟨R, hR⟩ : ∃ R : ℝ, R = S.Dstar / S.du := ⟨_, rfl⟩
  rw [← hR] at hPA'
  have hR0 : 0 < R := by rw [hPA']; positivity
  have hdu : S.du ≠ 0 := by
    intro h
    rw [h, div_zero] at hR
    linarith
  have hD : S.Dstar = R * S.du := by rw [hR, div_mul_cancel₀ _ hdu]
  have hG2e : Real.exp X ^ 2 = Real.exp (2 * X) := by
    rw [← Real.exp_nat_mul]; norm_num
  have hRb : Real.exp (2 * X) / C0 ≤ R ∧ R ≤ Real.exp (2 * X) * C0 := by
    obtain ⟨c1, c2⟩ := hCh
    rw [hG2e, hD] at c1 c2
    exact ratio_bounds (Real.exp_pos _) hC0 hdu c1 c2
  have hEab := abs_le.mp (hEa'.trans hf2)
  have hEa2 : S.Ea ≤ 2 := (Real.log_le_log_iff hEa (by norm_num)).mp hEab.2
  have hEa12 : 1 / 2 ≤ S.Ea := by
    have : Real.log (1 / 2) ≤ Real.log S.Ea := by
      rw [one_div, Real.log_inv]; exact hEab.1
    exact (Real.log_le_log_iff (by norm_num) hEa).mp this
  rw [hPA'] at hRb
  exact root_bounds hP0 hk1 hC0 hX0 hX8 hEa12 hEa2 hRb.1 hRb.2

theorem bracketBound : BracketBound := by
  intro k r m ka rd g VV Vu hm hk hrd hka hg hVV hVu om
  have hpi : 0 < Real.pi := Real.pi_pos
  have h2pi : (1 : ℝ) ≤ 2 * Real.pi := by linarith [Real.pi_gt_three]
  have hrd0 : 0 < rd := by linarith
  have hka0 : 0 < ka := by rw [hka]; positivity
  have hg0 : 0 < g := by linarith
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  obtain ⟨e, he⟩ : ∃ e : ℕ, e = m * (m - 1) / 2 := ⟨_, rfl⟩
  have he2 : e = (r + 1) * (2 * r + 1) := by
    rw [he, hm]
    have : (2 * r + 2) * (2 * r + 2 - 1) = 2 * ((r + 1) * (2 * r + 1)) := by
      have : 2 * r + 2 - 1 = 2 * r + 1 := by omega
      rw [this]; ring
    rw [this]; simp
  have hmR : (m : ℝ) = 2 * r + 2 := by rw [hm]; push_cast; ring
  have heR : (e : ℝ) = ((r : ℝ) + 1) * (2 * r + 1) := by rw [he2]; push_cast; ring
  have hr0 : (0 : ℝ) ≤ r := Nat.cast_nonneg _
  obtain ⟨B, hB⟩ : ∃ B : ℝ, B = (ka ^ e)⁻¹ * rd ^ (-(((m : ℝ) - 1) / 2)) * g ^ e := ⟨_, rfl⟩
  have hom : om = B ^ ((1 : ℝ) / (k : ℝ)) := by rw [hB, he]
  have hB0 : 0 < B := by rw [hB]; positivity
  have hlogka : Real.log ka = Real.log (2 * Real.pi) - Real.log rd := by
    rw [hka, Real.log_div (by positivity) hrd0.ne']
  have hlogB : Real.log B = e * (Real.log g + Real.log rd - Real.log (2 * Real.pi)) -
      ((m : ℝ) - 1) / 2 * Real.log rd := by
    rw [hB, Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
      Real.log_inv, Real.log_pow, Real.log_pow, Real.log_rpow hrd0, hlogka]
    ring
  have hl1 : 0 ≤ Real.log rd := Real.log_nonneg hrd
  have hl2 : 0 ≤ Real.log (2 * Real.pi) := Real.log_nonneg h2pi
  have hl3 : Real.log (2 * Real.pi) ≤ Real.log g := Real.log_le_log (by positivity) hg
  have hlow : 0 ≤ Real.log B := by
    rw [hlogB, heR, hmR]
    have t1 : 0 ≤ ((r : ℝ) + 1) * (2 * r + 1) * (Real.log g - Real.log (2 * Real.pi)) := by
      apply mul_nonneg (by positivity); linarith
    have t2 : 0 ≤ (((r : ℝ) + 1) * (2 * r + 1) - (2 * r + 2 - 1) / 2) * Real.log rd := by
      apply mul_nonneg _ hl1
      nlinarith
    nlinarith
  have hup : Real.log B ≤ (m : ℝ) ^ 2 * (Real.log g + Real.log rd) / 2 := by
    rw [hlogB, heR, hmR]
    have t1 : 0 ≤ ((r : ℝ) + 1) * (2 * r + 1) * Real.log (2 * Real.pi) := by positivity
    have t2 : 0 ≤ ((2 * (r : ℝ) + 2 - 1) / 2) * Real.log rd := by
      apply mul_nonneg _ hl1
      linarith
    have t3 : 0 ≤ ((2 * (r : ℝ) + 2) ^ 2 / 2 - ((r : ℝ) + 1) * (2 * r + 1)) *
        (Real.log g + Real.log rd) := by
      apply mul_nonneg
      · nlinarith
      · linarith
    nlinarith
  have hB1 : 1 ≤ B := (Real.log_nonneg_iff hB0).mp hlow
  refine ⟨?_, ?_, ?_⟩
  · rw [hom]
    exact Real.one_le_rpow hB1 (by positivity)
  · rw [hom, Real.rpow_def_of_pos hB0]
    apply Real.exp_le_exp.mpr
    have : (m : ℝ) ^ 2 * (Real.log g + Real.log rd) / (2 * k) =
        (m : ℝ) ^ 2 * (Real.log g + Real.log rd) / 2 * (1 / k) := by
      field_simp
    rw [this]
    exact mul_le_mul_of_nonneg_right hup (by positivity)
  · have hX : 0 ≤ (ka ^ (m - 1))⁻¹ * g ^ m := by positivity
    have hP : TcritPow k m ka rd g VV Vu = ((ka ^ (m - 1))⁻¹ * g ^ m) ^ k * B * (VV / Vu) := by
      unfold TcritPow
      rw [hB, ← he, pow_add, pow_add, pow_mul, mul_comm k m, pow_mul, mul_pow, inv_pow, mul_inv]
      ring
    unfold Tcrit
    rw [hP, Real.mul_rpow (by positivity) (by positivity), Real.mul_rpow (by positivity) hB0.le,
      one_div, Real.pow_rpow_inv_natCast hX (by omega), hom, one_div]

end Formalism.FourierDecayAlt.P.Sz2

namespace Formalism.FourierDecayAlt.P

theorem zeta_tail_bound : Formalism.FourierDecayAlt.Sz.ZetaTail := Sz2.zetaTail

theorem exponent_sizes : Formalism.FourierDecayAlt.Sz.EaSize := Sz2.eaSize

theorem corollary_a_of_proposition_a : Formalism.FourierDecayAlt.Sz.CorA := Sz2.corA_of_propA massRatioFormula

theorem bracket_bound_alt : Formalism.FourierDecayAlt.Sz.BracketBound := Sz2.bracketBound

end Formalism.FourierDecayAlt.P
