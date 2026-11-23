import Mathlib
import Development.AutomorphicArithmetic.ResidueCharacters.NumParameters
import Development.AutomorphicArithmetic.ResidueCharacters.NumBounds

noncomputable section

open NumberField Formalism Formalism.BasicNotions

namespace UpperTheory.N.Num

variable {D : D7}

theorem hB_bounds (L : SizeData₂ D) (P : ParameterChoice' D L) :
    L.sc.b ≤ L.sc.b + L.Sc + L.etaSz + D.R.t + 2 ∧ L.sc.b + L.Sc + L.etaSz + D.R.t + 2 ≤ 6 * L.sc.b := by
  obtain ⟨h1, h2, h3⟩ := sizes_le_b L P
  have hb := one_le_b L
  have := L.Sc_pos
  have := L.etaSz_pos
  have : (0 : ℝ) ≤ D.R.t := Nat.cast_nonneg _
  constructor <;> linarith

theorem level_le' (D : D7) {l : ℕ} (hl : l.Prime)
    (hfac : D.host.condN.factorization l = D.host.QS.factorization l) {x C : ℝ} (hx : 1 ≤ Real.log x) (hx0 : 0 < x) (hC : 1 ≤ C)
    (hn : (D.R.n : ℝ) ≤ x ^ C) : ((max 1 (D.host.condN.factorization l) : ℕ) : ℝ) ≤ 3 * C * Real.log x := by
  rw [hfac]
  have hCx : 1 ≤ C * Real.log x := one_le_mul_of_one_le_of_one_le hC hx
  have h1 : 2 ^ D.host.QS.factorization l ≤ D.R.n ^ 2 :=
    (Nat.pow_le_pow_left hl.two_le _).trans
      ((Nat.le_of_dvd D.host.QS_pos (Nat.ordProj_dvd _ _)).trans D.host.QS_le)
  have h2 : (2 : ℝ) ^ D.host.QS.factorization l ≤ (x ^ C) ^ 2 := by
    have : ((2 : ℝ)) ^ D.host.QS.factorization l ≤ (D.R.n : ℝ) ^ 2 := by exact_mod_cast h1
    exact this.trans (pow_le_pow_left₀ (Nat.cast_nonneg _) hn 2)
  have h3 := Real.log_le_log (by positivity) h2
  rw [Real.log_pow, Real.log_pow, Real.log_rpow hx0] at h3
  have h4 := Real.log_two_gt_d9
  have h5 : (D.host.QS.factorization l : ℝ) ≤ 3 * C * Real.log x := by
    have h0 : (0 : ℝ) ≤ D.host.QS.factorization l := Nat.cast_nonneg _
    push_cast at h3
    nlinarith
  rw [Nat.cast_max]
  refine max_le ?_ h5
  push_cast
  linarith

theorem factorization_condN' (D : D7) {l : ℕ} (hq : l ≠ D.host.q) (hd : l ≠ D.host.d) :
    D.host.condN.factorization l = D.host.QS.factorization l := by
  have pq := D.host.hyp.1
  have pd := D.host.hyp.2.1
  show (D.host.QS * D.host.q * D.host.d).factorization l = _
  rw [Nat.factorization_mul (mul_ne_zero D.host.QS_pos.ne' pq.ne_zero) pd.ne_zero,
    Nat.factorization_mul D.host.QS_pos.ne' pq.ne_zero, pq.factorization, pd.factorization]
  simp [Finsupp.single_apply, hq.symm, hd.symm]

set_option maxHeartbeats 800000 in
theorem cost_le' (L : SizeData₂ D) (P : ParameterChoice' D L) {A B C0 : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (hC : 1 ≤ C0)
    (hx : 1 ≤ Real.log L.sc.x) (hn : (D.R.n : ℝ) ≤ L.sc.x ^ C0) (ht : (D.R.t : ℝ) ≤ L.sc.x ^ C0) {l : ℕ}
    (hl : l.Prime) (hfac : D.host.condN.factorization l = D.host.QS.factorization l) {C : ℝ}
    (hC' : 18 * A * C0 + 2 * B * (3 * C0 + 9) + 5 * C0 + 1 ≤ C) :
    A * D.R.f * D.R.m * (L.sc.b + L.Sc + L.etaSz + D.R.t + 2) * ((max 1 (D.host.condN.factorization l) : ℕ) : ℝ) +
      B * (D.R.f : ℝ) ^ 2 * (D.R.t : ℝ) ^ 2 * D.R.nV *
        lam l (max 1 (D.host.condN.factorization l)) (L.sc.b + L.Sc + L.etaSz + D.R.t + 2) ≤
      C * D.R.f * D.R.m * L.sc.b * Real.log L.sc.x + C * L.sc.x ^ C * L.sc.L ^ 2 := by
  have hx1 : 1 < L.sc.x := L.sc.one_lt_alt
  have hx0 : 0 < L.sc.x := by linarith
  have hS := level_le' D hl hfac hx hx0 hC hn
  obtain ⟨hh1, hh2⟩ := hB_bounds L P
  obtain ⟨r1, r2, r3, r4, r5, r6, r7⟩ := ranks D
  have hb := one_le_b L
  have hL := one_le_L L
  set s : ℕ := max 1 (D.host.condN.factorization l)
  set h : ℝ := L.sc.b + L.Sc + L.etaSz + D.R.t + 2
  set x := L.sc.x
  have hAC : 0 ≤ A * C0 := by positivity
  have hBC : 0 ≤ B * (3 * C0 + 9) := by positivity
  have t1 : A * D.R.f * D.R.m * h * (s : ℝ) ≤ C * D.R.f * D.R.m * L.sc.b * Real.log x := by
    calc A * D.R.f * D.R.m * h * (s : ℝ) ≤ A * D.R.f * D.R.m * (6 * L.sc.b) * (3 * C0 * Real.log x) := by gcongr
      _ = (18 * A * C0) * (D.R.f * D.R.m * L.sc.b * Real.log x) := by ring
      _ ≤ C * (D.R.f * D.R.m * L.sc.b * Real.log x) := by gcongr; linarith
      _ = _ := by ring
  have hlog : Real.logb l (2 * h) ≤ 2 * L.sc.L + 6 := by
    have a : Real.log (2 * h) ≤ L.sc.L + 3 := by
      have a1 : Real.log (2 * h) ≤ Real.log (12 * L.sc.b) := Real.log_le_log (by linarith) (by linarith)
      have a2 : Real.log L.sc.b = L.sc.L := Real.log_exp _
      have a3 : Real.log 12 ≤ 3 := by
        rw [Real.log_le_iff_le_exp (by norm_num)]
        have := Real.add_one_le_exp (1 : ℝ)
        have e : Real.exp 3 = Real.exp 1 ^ 3 := by rw [← Real.exp_nat_mul]; norm_num
        have := Real.exp_one_gt_d9
        rw [e]
        calc (12 : ℝ) ≤ 2.7 ^ 3 := by norm_num
          _ ≤ Real.exp 1 ^ 3 := by gcongr; linarith
      rw [Real.log_mul (x := 12) (by norm_num) (by linarith), a2] at a1
      linarith
    have b : (1 / 2 : ℝ) ≤ Real.log l := by
      have : Real.log 2 ≤ Real.log l := Real.log_le_log (by norm_num) (by exact_mod_cast hl.two_le)
      have := Real.log_two_gt_d9
      linarith
    unfold Real.logb
    rw [div_le_iff₀ (by linarith)]
    nlinarith
  have hlx : Real.log x ≤ x := (Real.log_le_sub_one_of_pos hx0).trans (by linarith)
  have hΛ : lam l s h ≤ (3 * C0 + 9) * (x * L.sc.L) := by
    have c1 : 1 ≤ x * L.sc.L := one_le_mul_of_one_le_of_one_le hx1.le hL
    have c2 : L.sc.L ≤ x * L.sc.L := by nlinarith
    have c3 : x ≤ x * L.sc.L := by nlinarith
    have c4 : 3 * C0 * Real.log x ≤ 3 * C0 * (x * L.sc.L) := by gcongr; linarith
    unfold lam
    nlinarith
  have hΛ0 : 0 ≤ lam l s h := by linarith [one_le_lam (s := s) hl.two_le (show 1 ≤ h by linarith)]
  have hP : 0 < x ^ C0 := Real.rpow_pos_of_pos hx0 _
  have hpow : (x ^ C0) ^ 5 * x ≤ x ^ C := by
    have e : (x ^ C0) ^ 5 * x = x ^ (5 * C0 + 1) := by
      rw [Real.rpow_add hx0, Real.rpow_one, mul_comm 5 C0, Real.rpow_mul hx0.le]
      norm_cast
    rw [e]
    exact Real.rpow_le_rpow_of_exponent_le hx1.le (by linarith)
  have hf : (D.R.f : ℝ) ≤ x ^ C0 := by linarith
  have hV : (D.R.nV : ℝ) ≤ 2 * x ^ C0 := by linarith
  have t2 : B * (D.R.f : ℝ) ^ 2 * (D.R.t : ℝ) ^ 2 * D.R.nV * lam l s h ≤ C * x ^ C * L.sc.L ^ 2 := by
    calc B * (D.R.f : ℝ) ^ 2 * (D.R.t : ℝ) ^ 2 * D.R.nV * lam l s h
        ≤ B * (x ^ C0) ^ 2 * (x ^ C0) ^ 2 * (2 * x ^ C0) * ((3 * C0 + 9) * (x * L.sc.L)) := by gcongr
      _ = (2 * B * (3 * C0 + 9)) * ((x ^ C0) ^ 5 * x) * (L.sc.L * 1) := by ring
      _ ≤ C * x ^ C * (L.sc.L * L.sc.L) := by
          have : 0 ≤ C := by linarith
          have h9 : 2 * B * (3 * C0 + 9) ≤ C := by linarith
          gcongr
      _ = _ := by ring
  linarith

theorem cost_le (L : SizeData₂ D) (P : ParameterChoice' D L) {A B C0 : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (hC : 1 ≤ C0)
    (hx : 1 ≤ Real.log L.sc.x) (hn : (D.R.n : ℝ) ≤ L.sc.x ^ C0) (ht : (D.R.t : ℝ) ≤ L.sc.x ^ C0) {l : ℕ}
    (hs : l ∈ D.host.small) {C : ℝ} (hC' : 18 * A * C0 + 2 * B * (3 * C0 + 9) + 5 * C0 + 1 ≤ C) :
    A * D.R.f * D.R.m * (L.sc.b + L.Sc + L.etaSz + D.R.t + 2) * ((max 1 (D.host.condN.factorization l) : ℕ) : ℝ) +
      B * (D.R.f : ℝ) ^ 2 * (D.R.t : ℝ) ^ 2 * D.R.nV *
        lam l (max 1 (D.host.condN.factorization l)) (L.sc.b + L.Sc + L.etaSz + D.R.t + 2) ≤
      C * D.R.f * D.R.m * L.sc.b * Real.log L.sc.x + C * L.sc.x ^ C * L.sc.L ^ 2 :=
  cost_le' L P hA hB hC hx hn ht (Nat.mem_primeFactors.1 hs).1 (factorization_condN D hs) hC'

end UpperTheory.N.Num

end
