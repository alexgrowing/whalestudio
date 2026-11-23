import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SizeAbsorption.ExpPowEq

noncomputable section

namespace PI.SzEatI.W

open Formalism.BasicNotions Formalism.MainNotions.G

private lemma one_le_rpow_of_one_le_of_nonneg (x z : ℝ) (hx : 1 ≤ x) (hz : 0 ≤ z) : 1 ≤ x ^ z := by
  have h := Real.rpow_le_rpow zero_le_one hx hz
  rwa [Real.one_rpow] at h

private lemma exists_log_le_rpow_and_mul_exp_le_exp_rpow (ε C : ℝ) (hε : 0 < ε) (hC : 0 < C) :
    ∃ x0 : ℝ, ∀ x : ℝ, 1 < x → x0 ≤ x →
      Real.log x ≤ x ^ (ε / 3) ∧
        C * x ^ 5 * (Real.exp (x ^ (ε / 3)) * Real.exp (x ^ (ε / 3))) ≤ Real.exp (x ^ ε) := by
  have hε0 : ε ≠ 0 := hε.ne'
  obtain ⟨B, hB⟩ : ∃ B : ℝ, B = 6 / ε := ⟨_, rfl⟩
  have hB0 : 0 < B := by rw [hB]; exact div_pos (by norm_num) hε
  have h3 : B * (ε / 6) = 1 := by rw [hB]; field_simp
  obtain ⟨M, hM⟩ : ∃ M : ℝ, M = |Real.log C| + 5 * B + 2 := ⟨_, rfl⟩
  have hlC : Real.log C ≤ |Real.log C| := le_abs_self _
  have hM1 : 1 ≤ M := by have := abs_nonneg (Real.log C); rw [hM]; linarith
  have hBM : B ≤ M := by have := abs_nonneg (Real.log C); rw [hM]; linarith
  refine ⟨M ^ B, fun x hx hx0 => ?_⟩
  have hxpos : 0 < x := by linarith
  obtain ⟨s, hs⟩ : ∃ s : ℝ, s = x ^ (ε / 6) := ⟨_, rfl⟩
  have hMs : M ≤ s := by
    have h1 : (M ^ B) ^ (ε / 6) ≤ x ^ (ε / 6) :=
      Real.rpow_le_rpow (Real.rpow_nonneg (by linarith) _) hx0 (by linarith)
    have h2 : (M ^ B) ^ (ε / 6) = M := by
      rw [← Real.rpow_mul (by linarith), h3, Real.rpow_one]
    rw [hs]; linarith
  have hs1 : 1 ≤ s := le_trans hM1 hMs
  have hlog : Real.log x ≤ B * s := by
    have hsp : 0 < s := by linarith
    have h2 : Real.log s ≤ s - 1 := Real.log_le_sub_one_of_pos hsp
    rw [hs, Real.log_rpow hxpos, ← hs] at h2
    calc Real.log x = B * (ε / 6 * Real.log x) := by rw [← mul_assoc, h3, one_mul]
      _ ≤ B * (s - 1) := mul_le_mul_of_nonneg_left h2 hB0.le
      _ ≤ B * s := by linarith
  have ht : x ^ (ε / 3) = s ^ 2 := by
    rw [hs, ← Real.rpow_natCast, ← Real.rpow_mul hxpos.le]; congr 1; push_cast; ring
  have hu : x ^ ε = s ^ 6 := by
    rw [hs, ← Real.rpow_natCast, ← Real.rpow_mul hxpos.le]; congr 1; push_cast; ring
  constructor
  · rw [ht]
    have h4 : B * s ≤ s * s := mul_le_mul_of_nonneg_right (le_trans hBM hMs) (by linarith)
    nlinarith [hlog, h4]
  · rw [ht, hu]
    have h5 : Real.log (x ^ 5) = 5 * Real.log x := by rw [Real.log_pow]; norm_num
    have hx5 : x ^ 5 = Real.exp (5 * Real.log x) := by
      rw [← h5, Real.exp_log (pow_pos hxpos 5)]
    have key : C * x ^ 5 * (Real.exp (s ^ 2) * Real.exp (s ^ 2)) =
        Real.exp (Real.log C + 5 * Real.log x + (s ^ 2 + s ^ 2)) := by
      rw [Real.exp_add, Real.exp_add, Real.exp_add, Real.exp_log hC, ← hx5]
    rw [key]
    apply Real.exp_le_exp.mpr
    have hs2 : 1 ≤ s ^ 2 := by nlinarith [hs1]
    have e2 : |Real.log C| ≤ |Real.log C| * s ^ 2 := by
      nlinarith [mul_nonneg (abs_nonneg (Real.log C)) (sub_nonneg.2 hs2)]
    have e3 : B * s ≤ B * s ^ 2 := mul_le_mul_of_nonneg_left (by nlinarith [hs1]) hB0.le
    have e4 : M * s ^ 2 ≤ s * s ^ 2 := mul_le_mul_of_nonneg_right hMs (sq_nonneg s)
    rw [hM] at e4
    have hs3 : 1 ≤ s ^ 3 := by nlinarith [mul_nonneg (sub_nonneg.2 hs1) (sq_nonneg s), hs2]
    have e5 : s * s ^ 2 ≤ s ^ 6 := by
      nlinarith [mul_nonneg (pow_nonneg (by linarith : (0:ℝ) ≤ s) 3) (sub_nonneg.2 hs3)]
    nlinarith [hlC, hlog, e2, e3, e4, e5]

private lemma sq_mul_add_abs_mul_nonneg (N A B C d1 d2 : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B) (hC : 0 ≤ C) :
    0 ≤ N ^ 2 * (A + B) + |d1| * N ^ 2 * C + 2 * |d2| * C ^ 2 :=
  add_nonneg (add_nonneg (mul_nonneg (sq_nonneg N) (add_nonneg hA hB))
    (mul_nonneg (mul_nonneg (abs_nonneg d1) (sq_nonneg N)) hC))
    (mul_nonneg (mul_nonneg (by norm_num) (abs_nonneg d2)) (sq_nonneg C))

private lemma sq_mul_add_abs_mul_le_mul_sq (N A B C d1 d2 E V : ℝ) (hA0 : 0 ≤ A) (hA : A ≤ 13 * V) (hB0 : 0 ≤ B)
    (hB : B ≤ 5 * V) (hC0 : 0 ≤ C) (hC : C ≤ 3 * V) (hN : N ^ 2 ≤ E) (hE : 1 ≤ E) (hV : 1 ≤ V) :
    N ^ 2 * (A + B) + |d1| * N ^ 2 * C + 2 * |d2| * C ^ 2 ≤
      (18 + 3 * |d1| + 18 * |d2|) * E * V ^ 2 := by
  have hN0 : 0 ≤ N ^ 2 := sq_nonneg N
  have hV2 : V ≤ V ^ 2 := by nlinarith
  have hE0 : 0 ≤ E := by linarith
  have e1 : N ^ 2 * (A + B) ≤ E * (18 * V) := mul_le_mul hN (by linarith) (by linarith) hE0
  have e2 : |d1| * N ^ 2 * C ≤ |d1| * E * (3 * V) :=
    mul_le_mul (mul_le_mul_of_nonneg_left hN (abs_nonneg _)) hC hC0
      (mul_nonneg (abs_nonneg _) hE0)
  have e3 : 2 * |d2| * C ^ 2 ≤ 2 * |d2| * (3 * V) ^ 2 := by
    apply mul_le_mul_of_nonneg_left _ (mul_nonneg (by norm_num) (abs_nonneg _))
    rw [sq, sq]; exact mul_le_mul hC hC hC0 (by linarith)
  have f1 : E * V ≤ E * V ^ 2 := mul_le_mul_of_nonneg_left hV2 hE0
  have f2 : |d1| * E * V ≤ |d1| * E * V ^ 2 :=
    mul_le_mul_of_nonneg_left hV2 (mul_nonneg (abs_nonneg _) hE0)
  have f3 : |d2| * V ^ 2 * 1 ≤ |d2| * V ^ 2 * E :=
    mul_le_mul_of_nonneg_left hE (mul_nonneg (abs_nonneg d2) (sq_nonneg V))
  nlinarith [e1, e2, e3, f1, f2, f3]

private lemma fin_lemma_5 (x n T R C0 V e : ℝ) (hx : 0 < x) (hn0 : 0 ≤ n) (hn : n ≤ x ^ 3)
    (hT : 0 < T) (hR : R ≤ C0 * T * V ^ 2) (he : 0 < e) (hV : V ^ 2 * e ^ 2 ≤ x)
    (hC0 : 0 ≤ C0) : x * n * T * R ≤ C0 / e ^ 2 * x ^ 5 * (T * T) := by
  have hxn : 0 ≤ x * n * T := mul_nonneg (mul_nonneg hx.le hn0) hT.le
  have h1 : x * n * T * R ≤ x * n * T * (C0 * T * V ^ 2) := mul_le_mul_of_nonneg_left hR hxn
  have hK : 0 ≤ C0 * T * V ^ 2 := mul_nonneg (mul_nonneg hC0 hT.le) (sq_nonneg V)
  have h2 : x * n * T * (C0 * T * V ^ 2) ≤ x * x ^ 3 * T * (C0 * T * V ^ 2) :=
    mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hn hx.le) hT.le) hK
  have he2 : 0 < e ^ 2 := pow_pos he 2
  have h3 : V ^ 2 ≤ x / e ^ 2 := by
    first
      | (rw [le_div_iff₀ he2]; exact hV)
      | (rw [le_div_iff he2]; exact hV)
      | (calc V ^ 2 = V ^ 2 * e ^ 2 / e ^ 2 := by field_simp
          _ ≤ x / e ^ 2 := by gcongr)
  have h4 : x * x ^ 3 * T * (C0 * T * V ^ 2) ≤ x * x ^ 3 * T * (C0 * T * (x / e ^ 2)) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h3 (mul_nonneg hC0 hT.le))
      (mul_nonneg (mul_nonneg hx.le (pow_nonneg hx.le 3)) hT.le)
  have h5 : x * x ^ 3 * T * (C0 * T * (x / e ^ 2)) = C0 / e ^ 2 * x ^ 5 * (T * T) := by ring
  linarith

set_option maxHeartbeats 800000 in

theorem stepA : StepA := by
  unfold StepA
  intro K eps
  by_cases heps : 0 < eps
  swap
  · exact ⟨0, fun D L hL _ _ => (heps (hL ▸ L.sc.eps_pos)).elim⟩
  obtain ⟨x0, hx0⟩ :=
    exists_log_le_rpow_and_mul_exp_le_exp_rpow eps ((18 + 3 * |K.dl1| + 18 * |K.dl2|) / eps ^ 2) heps (by positivity)
  refine ⟨x0, fun D L hL hx hS => ?_⟩
  subst hL
  have hx1 : 1 < L.sc.x := L.sc.one_lt_alt
  have hxpos : 0 < L.sc.x := by linarith
  have he0 : 0 < L.sc.eps := L.sc.eps_pos
  have he1 : L.sc.eps < 1 / 52 := L.sc.eps_lt
  have he0' : L.sc.eps ≠ 0 := he0.ne'
  obtain ⟨hlt, hgrow⟩ := hx0 L.sc.x hx1 hx
  unfold Formalism.MainNotions.SizesAt at hS
  obtain ⟨hN, -, -, -, -, -, -, -, -, -, -, -, -, -, hNodes, -, hDel, -⟩ := hS
  unfold Formalism.MainNotions.SizeN Formalism.MainNotions.szTh at hN
  obtain ⟨hn_lo, hn_up⟩ := hN
  unfold Formalism.MainNotions.SizeNodes at hNodes
  obtain ⟨-, -, -, hNd4, -⟩ := hNodes
  unfold Formalism.MainNotions.SizeDel at hDel
  obtain ⟨hDel1, -, hDel3, -⟩ := hDel

  have hn1 : (1:ℝ) ≤ D.R.n := le_trans (one_le_rpow_of_one_le_of_nonneg _ _ hx1.le (by linarith)) hn_lo
  have hnpos : (0:ℝ) < D.R.n := by linarith
  have hn3 : (D.R.n : ℝ) ≤ L.sc.x ^ 3 := by
    have h := Real.rpow_le_rpow_of_exponent_le hx1.le
      (show 2 + 8 * L.sc.eps + L.sc.eps / 100 ≤ ((3:ℕ):ℝ) by push_cast; linarith)
    rw [Real.rpow_natCast] at h
    linarith
  have hm : (1:ℝ) ≤ D.R.m := by
    rcases Nat.eq_zero_or_pos D.R.m with h | h
    · exfalso
      rw [h, Nat.cast_zero, div_zero] at hNd4
      have : (0:ℝ) ≤ 4 * (D.R.N 0 : ℝ) ^ 3 + 2 * D.R.t := by positivity
      linarith
    · exact Nat.one_le_cast.mpr h
  have hNm0 : (0:ℝ) ≤ Nm D := by unfold Nm; positivity
  have hNmDel : Nm D ≤ (D.s.Del : ℝ) := by
    have h10 : (1:ℝ) ≤ (D.R.m : ℝ) ^ 10 := by
      first
        | exact one_le_pow₀ hm
        | exact one_le_pow_of_one_le' hm 10
        | exact one_le_pow_of_one_le hm 10
        | (have h := pow_le_pow_left zero_le_one hm 10; rwa [one_pow] at h)
    calc Nm D = Nm D * 1 := (mul_one _).symm
      _ ≤ Nm D * (D.R.m : ℝ) ^ 10 := mul_le_mul_of_nonneg_left h10 hNm0
      _ ≤ (D.s.Del : ℝ) := hDel1
  have hNmE : Nm D ≤ Real.exp (L.sc.x ^ (L.sc.eps / 4) / 2) := by
    by_cases h : (D.s.Del : ℝ) ≤ 0
    · exact le_trans (le_trans hNmDel h) (Real.exp_pos _).le
    · push_neg at h
      calc Nm D ≤ (D.s.Del : ℝ) := hNmDel
          _ = Real.exp (Real.log (D.s.Del : ℝ)) := (Real.exp_log h).symm
          _ ≤ Real.exp (L.sc.x ^ (L.sc.eps / 4) / 2) := Real.exp_le_exp.mpr hDel3

  have hu1 : 1 ≤ L.sc.x ^ L.sc.eps := one_le_rpow_of_one_le_of_nonneg _ _ hx1.le he0.le
  have hup : 0 < L.sc.x ^ L.sc.eps := by linarith
  have ht1 : 1 ≤ L.sc.x ^ (L.sc.eps / 3) := one_le_rpow_of_one_le_of_nonneg _ _ hx1.le (by linarith)
  have hqt : L.sc.x ^ (L.sc.eps / 4) ≤ L.sc.x ^ (L.sc.eps / 3) :=
    Real.rpow_le_rpow_of_exponent_le hx1.le (by linarith)
  have htu : L.sc.x ^ (L.sc.eps / 3) ≤ L.sc.x ^ L.sc.eps :=
    Real.rpow_le_rpow_of_exponent_le hx1.le (by linarith)
  have hT1 : 1 ≤ Real.exp (L.sc.x ^ (L.sc.eps / 3)) := by
    linarith [Real.add_one_le_exp (L.sc.x ^ (L.sc.eps / 3))]
  have hNm2 : Nm D ^ 2 ≤ Real.exp (L.sc.x ^ (L.sc.eps / 3)) := by
    have h1 : Nm D ^ 2 ≤ Real.exp (L.sc.x ^ (L.sc.eps / 4) / 2) ^ 2 := by
      rw [sq, sq]; exact mul_le_mul hNmE hNmE hNm0 (le_trans hNm0 hNmE)
    have h2 : Real.exp (L.sc.x ^ (L.sc.eps / 4) / 2) ^ 2 = Real.exp (L.sc.x ^ (L.sc.eps / 4)) := by
      rw [sq, ← Real.exp_add]; congr 1; ring
    rw [h2] at h1
    exact le_trans h1 (Real.exp_le_exp.mpr hqt)

  have ha : L.sc.a = L.sc.x * Real.exp (L.sc.x ^ L.sc.eps) := rfl
  have hb : L.sc.b = Real.exp (L.sc.x ^ L.sc.eps) := rfl
  have hX' : L.sc.X' = Real.exp (L.sc.x ^ (L.sc.eps / 3)) := rfl
  have hb' : L.sc.b' = L.sc.a / L.sc.X' := rfl
  have ha0 : L.sc.a ≠ 0 := by rw [ha]; exact mul_ne_zero hxpos.ne' (Real.exp_pos _).ne'
  have hXpp : L.sc.X'' D.R.n = L.sc.x * D.R.n * Real.exp (L.sc.x ^ (L.sc.eps / 3)) := by
    have e1 : L.sc.X'' D.R.n = L.sc.a / (L.sc.a / L.sc.X' / (L.sc.x * D.R.n)) := rfl
    rw [e1, hX']
    have hn0 : (D.R.n : ℝ) ≠ 0 := hnpos.ne'
    have hx0' : L.sc.x ≠ 0 := hxpos.ne'
    have hE0 : Real.exp (L.sc.x ^ (L.sc.eps / 3)) ≠ 0 := (Real.exp_pos _).ne'
    first
      | (field_simp; done)
      | (field_simp; ring)

  have g1 : L.sc.b' ≤ L.sc.b := by
    have hxt : L.sc.x ≤ Real.exp (L.sc.x ^ (L.sc.eps / 3)) := by
      calc L.sc.x = Real.exp (Real.log L.sc.x) := (Real.exp_log hxpos).symm
        _ ≤ _ := Real.exp_le_exp.mpr hlt
    rw [hb', ha, hX', hb]
    have hEp := Real.exp_pos (L.sc.x ^ L.sc.eps)
    have hTp := Real.exp_pos (L.sc.x ^ (L.sc.eps / 3))
    first
      | (rw [div_le_iff₀ hTp]; linarith [mul_le_mul_of_nonneg_left hxt hEp.le])
      | (rw [div_le_iff hTp]; linarith [mul_le_mul_of_nonneg_left hxt hEp.le])

  have hlogXeq : Real.log (L.sc.X'' D.R.n) =
      Real.log L.sc.x + Real.log D.R.n + L.sc.x ^ (L.sc.eps / 3) := by
    rw [hXpp, Real.log_mul (mul_pos hxpos hnpos).ne' (Real.exp_pos _).ne', Real.log_exp,
      Real.log_mul hxpos.ne' hnpos.ne']
  have hlx0 : 0 < Real.log L.sc.x := Real.log_pos hx1
  have hln0 : 0 ≤ Real.log (D.R.n : ℝ) := Real.log_nonneg hn1
  have g4 : 1 < L.sc.X'' D.R.n := by
    rw [hXpp]
    have h1 : L.sc.x ≤ L.sc.x * D.R.n := by
      linarith [mul_nonneg hxpos.le (sub_nonneg.2 hn1)]
    have h2 : L.sc.x * D.R.n ≤ L.sc.x * D.R.n * Real.exp (L.sc.x ^ (L.sc.eps / 3)) := by
      linarith [mul_nonneg (mul_pos hxpos hnpos).le (sub_nonneg.2 hT1)]
    linarith
  have g5 : 1 ≤ Real.log (L.sc.X'' D.R.n) := by rw [hlogXeq]; linarith

  have ha1 : 1 ≤ L.sc.a := by
    rw [ha]
    have hE1 : 1 ≤ Real.exp (L.sc.x ^ L.sc.eps) := by
      linarith [Real.add_one_le_exp (L.sc.x ^ L.sc.eps)]
    linarith [mul_nonneg (sub_nonneg.2 hx1.le) (sub_nonneg.2 hE1)]
  have hloga : Real.log L.sc.a = Real.log L.sc.x + L.sc.x ^ L.sc.eps := by
    rw [ha, Real.log_mul hxpos.ne' (Real.exp_pos _).ne', Real.log_exp]
  have hl1 : 0 ≤ Real.log (8 * (D.R.n : ℝ) * Nm D * L.sc.a) := by
    rcases eq_or_lt_of_le hNm0 with h | h
    · simp [← h]
    · apply Real.log_nonneg
      have hNm1 : (1:ℝ) ≤ Nm D := by
        have h' : (0:ℝ) < (D.R.N D.R.m : ℝ) := h
        have h'' : 0 < D.R.N D.R.m := by exact_mod_cast h'
        first
          | exact Nat.one_le_cast.mpr h''
          | (unfold Nm; exact_mod_cast h'')
      have h8 : (1:ℝ) ≤ 8 * (D.R.n : ℝ) := by linarith
      have h8N : (1:ℝ) ≤ 8 * (D.R.n : ℝ) * Nm D := by
        linarith [mul_nonneg (sub_nonneg.2 h8) (sub_nonneg.2 hNm1)]
      linarith [mul_nonneg (sub_nonneg.2 h8N) (sub_nonneg.2 ha1)]
  have hl2 : 0 ≤ Real.log (L.sc.X'' D.R.n) := by linarith
  have hl3 : 0 ≤ Real.log (2 * L.sc.a) := Real.log_nonneg (by linarith)
  have g2 : 0 ≤ Rt L K :=
    sq_mul_add_abs_mul_nonneg (Nm D) (Real.log (8 * (D.R.n : ℝ) * Nm D * L.sc.a)) (Real.log (L.sc.X'' D.R.n))
      (Real.log (2 * L.sc.a)) K.dl1 K.dl2 hl1 hl2 hl3

  have hlx : Real.log L.sc.x ≤ L.sc.x ^ L.sc.eps / L.sc.eps := by
    have h2 := Real.log_le_sub_one_of_pos hup
    rw [Real.log_rpow hxpos] at h2
    have h3 : L.sc.eps * (L.sc.x ^ L.sc.eps / L.sc.eps) = L.sc.x ^ L.sc.eps := by
      first
        | (field_simp; done)
        | (field_simp; ring)
    by_contra hc
    push_neg at hc
    have h4 := mul_lt_mul_of_pos_left hc he0
    rw [h3] at h4
    linarith
  obtain ⟨V, hV⟩ : ∃ V : ℝ, V = L.sc.x ^ L.sc.eps / L.sc.eps := ⟨_, rfl⟩
  rw [← hV] at hlx
  have hV0 : 0 < V := by rw [hV]; exact div_pos hup he0
  have huV : L.sc.x ^ L.sc.eps ≤ V := by
    have h3 : L.sc.eps * V = L.sc.x ^ L.sc.eps := by
      rw [hV]
      first
        | (field_simp; done)
        | (field_simp; ring)
    have h4 : L.sc.eps * V ≤ 1 * V :=
      mul_le_mul_of_nonneg_right (by linarith) hV0.le
    linarith
  have hV1 : 1 ≤ V := le_trans hu1 huV
  have hlogn : Real.log (D.R.n : ℝ) ≤ 3 * Real.log L.sc.x := by
    have h : Real.log (D.R.n : ℝ) ≤ Real.log (L.sc.x ^ 3) := by
      first
        | exact Real.log_le_log hnpos hn3
        | exact Real.log_le_log_of_le hnpos hn3
        | exact (Real.log_le_log_iff hnpos (lt_of_lt_of_le hnpos hn3)).2 hn3
    rw [Real.log_pow] at h
    push_cast at h
    linarith
  have hl1' : Real.log (8 * (D.R.n : ℝ) * Nm D * L.sc.a) ≤ 13 * V := by
    rcases eq_or_lt_of_le hNm0 with h | h
    · rw [← h, mul_zero, zero_mul, Real.log_zero]; linarith
    · have hN0' : Nm D ≠ 0 := h.ne'
      rw [Real.log_mul (mul_ne_zero (mul_ne_zero (by norm_num) hnpos.ne') hN0') ha0,
        Real.log_mul (mul_ne_zero (by norm_num) hnpos.ne') hN0',
        Real.log_mul (by norm_num) hnpos.ne']
      have h8 : Real.log 8 ≤ 8 - 1 := Real.log_le_sub_one_of_pos (by norm_num)
      have hlN : Real.log (Nm D) ≤ L.sc.x ^ (L.sc.eps / 4) / 2 := by
        have h' : Real.log (Nm D) ≤ Real.log (Real.exp (L.sc.x ^ (L.sc.eps / 4) / 2)) := by
          first
            | exact Real.log_le_log h hNmE
            | exact Real.log_le_log_of_le h hNmE
            | exact (Real.log_le_log_iff h (lt_of_lt_of_le h hNmE)).2 hNmE
        rwa [Real.log_exp] at h'
      linarith [hlogn, hlx, hloga, hqt, htu, huV, hV1]
  have hl2' : Real.log (L.sc.X'' D.R.n) ≤ 5 * V := by
    rw [hlogXeq]; linarith [hlogn, hlx, htu, huV]
  have hl3' : Real.log (2 * L.sc.a) ≤ 3 * V := by
    rw [Real.log_mul (by norm_num) ha0, hloga]
    have h2 : Real.log 2 ≤ 2 - 1 := Real.log_le_sub_one_of_pos (by norm_num)
    linarith
  have hR : Rt L K ≤ (18 + 3 * |K.dl1| + 18 * |K.dl2|) * Real.exp (L.sc.x ^ (L.sc.eps / 3)) * V ^ 2 :=
    sq_mul_add_abs_mul_le_mul_sq (Nm D) (Real.log (8 * (D.R.n : ℝ) * Nm D * L.sc.a)) (Real.log (L.sc.X'' D.R.n))
      (Real.log (2 * L.sc.a)) K.dl1 K.dl2 (Real.exp (L.sc.x ^ (L.sc.eps / 3))) V
      hl1 hl1' hl2 hl2' hl3 hl3' hNm2 hT1 hV1

  have hu2 : (L.sc.x ^ L.sc.eps) ^ 2 ≤ L.sc.x := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hxpos.le]
    have h := Real.rpow_le_rpow_of_exponent_le hx1.le
      (show L.sc.eps * ((2:ℕ):ℝ) ≤ 1 by push_cast; linarith)
    rwa [Real.rpow_one] at h
  have hV2 : V ^ 2 * L.sc.eps ^ 2 ≤ L.sc.x := by
    have h3 : V ^ 2 * L.sc.eps ^ 2 = (L.sc.x ^ L.sc.eps) ^ 2 := by
      rw [hV]
      first
        | (field_simp; done)
        | (field_simp; ring)
        | ring
    rw [h3]; exact hu2
  have hfin := fin_lemma_5 L.sc.x (D.R.n : ℝ) (Real.exp (L.sc.x ^ (L.sc.eps / 3))) (Rt L K)
    (18 + 3 * |K.dl1| + 18 * |K.dl2|) V L.sc.eps hxpos hnpos.le hn3 (Real.exp_pos _) hR he0 hV2
    (by positivity)
  refine ⟨g1, g2, ?_, g4, g5⟩
  rw [hXpp, hb]
  exact le_trans hfin hgrow

end PI.SzEatI.W
