import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.TameGeneratorWindow
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExplicitRanksBasicBoundsLargeScale
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.HostBoundsTwoMulRpowLogSqLe

noncomputable section

namespace GlobalTheory.ClassDuty

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab NumberField GlobalTheory.EX GlobalTheory.IndefiniteRowSideFullHecke.TameGeneratorWindow

theorem exists_large (eps A : ℝ) (he : 0 < eps) (hA : 0 < A) :
    ∃ x0 : ℝ, ∀ x ≥ x0, A * (x ^ (eps / 5) * Real.log x ^ 2) < x ^ (eps / 3) ∧ 2 ≤ x ^ (eps / 16) ∧ 44 ^ 3 ≤ x := by
  have h := (isLittleO_log_rpow_rpow_atTop (2 : ℝ) (s := 2 * eps / 15) (by positivity)).bound
    (c := 1 / (2 * A)) (by positivity)
  have h' := (tendsto_rpow_atTop (y := eps / 16) (by positivity)).eventually_ge_atTop 2
  obtain ⟨x0, hx0⟩ := Filter.eventually_atTop.mp ((h.and h').and (Filter.eventually_ge_atTop ((44 : ℝ) ^ 3)))
  refine ⟨x0, fun x hx => ?_⟩
  obtain ⟨⟨h1, h3⟩, h2⟩ := hx0 x hx
  have hx0 : 0 < x := by linarith [show (0 : ℝ) < 44 ^ 3 by norm_num]
  refine ⟨?_, h3, h2⟩
  rw [Real.norm_eq_abs, Real.norm_eq_abs, Real.rpow_two, abs_of_nonneg (sq_nonneg _),
    abs_of_nonneg (Real.rpow_nonneg hx0.le _)] at h1
  have e : x ^ (eps / 3) = x ^ (eps / 5) * x ^ (2 * eps / 15) := by
    rw [← Real.rpow_add hx0]; congr 1; ring
  have hp : 0 < x ^ (eps / 5) := Real.rpow_pos_of_pos hx0 _
  have hq : 0 < x ^ (2 * eps / 15) := Real.rpow_pos_of_pos hx0 _
  have h4 : A * Real.log x ^ 2 ≤ x ^ (2 * eps / 15) / 2 := by
    calc A * Real.log x ^ 2 ≤ A * (1 / (2 * A) * x ^ (2 * eps / 15)) := by gcongr
      _ = _ := by field_simp
  rw [e]
  nlinarith

theorem poly_lt {x w y : ℝ} (hx : 44 ^ 3 ≤ x) (hw : Real.log x ≤ w) (hy : 500 * w < y) :
    8 * x ^ (406 : ℝ) < Real.exp y := by
  have hx0 : 0 < x := by linarith [show (0 : ℝ) < 44 ^ 3 by norm_num]
  have hx1 : 1 ≤ x := by linarith [show (1 : ℝ) < 44 ^ 3 by norm_num]
  have hl : 0 ≤ Real.log x := Real.log_nonneg hx1
  calc 8 * x ^ (406 : ℝ) ≤ x * x ^ (406 : ℝ) := by
        gcongr; linarith [show (8 : ℝ) < 44 ^ 3 by norm_num]
    _ = x ^ (407 : ℝ) := by rw [show (407 : ℝ) = 1 + 406 by norm_num, Real.rpow_add hx0, Real.rpow_one]
    _ = Real.exp (Real.log x * 407) := Real.rpow_def_of_pos hx0 _
    _ < Real.exp y := Real.exp_lt_exp.2 (by linarith)

set_option maxHeartbeats 1000000 in

theorem windowsAt_of (eps : ℝ) (he : 0 < eps) (he' : eps < 1 / 52) (C : FC) (hC : Std C) :
    ∃ x0 : ℝ, ∀ (cD ch : ℝ) (D : D7) (L : SizeData₂ D), L.sc.eps = eps → x0 ≤ L.sc.x → Val C cD ch L → ParameterChoice' D L →
      WindowsAt L C.P.CY ∧ L.sc.X' ≤ lJ L := by
  have h8 : 1 ≤ C.P.Cpde := hC.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hY : 1 ≤ C.P.CY := hC.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2 _ (by simp [FC.cLast])
  obtain ⟨x1, h1⟩ := exists_large eps (500 + 2 * C.P.Cpde + 2 * C.P.CY) he (by linarith)
  obtain ⟨x2, h2⟩ := rank_basic_bounds eps he he'
  obtain ⟨x3, h3⟩ := hostBounds eps C.P.Cpde he he' h8
  refine ⟨max x1 (max x2 x3), fun cD ch D L hs hx h P => ?_⟩
  obtain ⟨hA, h16, h44⟩ := h1 _ ((le_max_left _ _).trans hx)
  obtain ⟨hf, hm, hr, hkr, -, -, hL1, -, -, -, -, -, -, ht, hN, hm1, hm2⟩ :=
    h2 _ _ hs (((le_max_left _ _).trans (le_max_right _ _)).trans hx) h.ranks
  obtain ⟨-, hq, -, hd, hcond, -, -, -, hp, hp'⟩ :=
    h3 _ _ _ hs (((le_max_right _ _).trans (le_max_right _ _)).trans hx) h.ranks h.host
  obtain ⟨⟨hn1, hn2⟩, ⟨hm1', hm2'⟩, ⟨hk1, hk2⟩, -⟩ := h.ranks
  have hg := h.host.2.2.2.2.1
  have hqp : D.host.q.Prime := D.host.hyp.1
  have hdp : D.host.d.Prime := D.host.hyp.2.1
  subst hs
  clear h1 h2 h3 hx
  set s := L.sc with hs
  have hx1 := s.one_lt_alt
  have hx0 : 0 < s.x := by linarith
  have mono : ∀ {a b : ℝ}, a ≤ b → s.x ^ a ≤ s.x ^ b := fun h => Real.rpow_le_rpow_of_exponent_le hx1.le h
  have one : ∀ {a : ℝ}, 0 ≤ a → 1 ≤ s.x ^ a := fun h => Real.one_le_rpow hx1.le h
  have hlog : 1 ≤ Real.log s.x := by
    rw [Real.le_log_iff_exp_le hx0]
    linarith [Real.exp_one_lt_d9, show (3 : ℝ) < 44 ^ 3 by norm_num]
  set w := s.x ^ (s.eps / 5) * Real.log s.x ^ 2 with hw
  have h5 : 1 ≤ s.x ^ (s.eps / 5) := one (by linarith)
  have hl2 : Real.log s.x ≤ Real.log s.x ^ 2 := le_self_pow₀ hlog two_ne_zero
  have hlw : Real.log s.x ≤ w := hl2.trans (le_mul_of_one_le_left (sq_nonneg _) h5)
  have h5w : s.x ^ (s.eps / 5) ≤ w := le_mul_of_one_le_right (by linarith) (hlog.trans hl2)
  have hw1 : 1 ≤ w := hlog.trans hlw
  set u := s.x ^ (s.eps / 3) with hu
  have hA1 : 500 * w < u := (mul_le_mul_of_nonneg_right (by linarith only [h8, hY]) (by linarith only [hw1])).trans_lt hA
  have hA2 : 2 * C.P.Cpde * w < u :=
    (mul_le_mul_of_nonneg_right (by linarith only [h8, hY]) (by linarith only [hw1])).trans_lt hA
  have hA3 : 2 * C.P.CY * w < u :=
    (mul_le_mul_of_nonneg_right (by linarith only [h8, hY]) (by linarith only [hw1])).trans_lt hA
  have hcond' : Real.log ((D.host.QS : ℝ) * D.host.q * D.host.d) ≤ 2 * w := by rw [hw, ← mul_assoc]; exact hcond
  have hpw : Real.log D.host.pde < u := by
    refine lt_of_le_of_lt ?_ hA2
    rw [hw, ← mul_assoc]; exact hp
  have hpw' : Real.log D.host.pde' < u := by
    refine lt_of_le_of_lt ?_ hA2
    rw [hw, ← mul_assoc]; exact hp'
  have hX : s.X' = Real.exp u := rfl
  have hpoly : 8 * s.x ^ (406 : ℝ) < s.X' := poly_lt h44 hlw hA1
  have hX1 : 1 ≤ s.X' := Real.one_le_exp (by linarith)
  have hu2 : 2 * u ≤ s.L := by
    have : s.L = s.x ^ (2 * s.eps / 3) * u := by
      rw [hu, ← Real.rpow_add hx0, Scale.L]; congr 1; ring
    rw [this]
    have := h16.trans (mono (b := 2 * s.eps / 3) (by linarith))
    exact mul_le_mul_of_nonneg_right this (by linarith)
  have hXb : s.X' * s.X' ≤ s.b := by
    rw [hX, ← Real.exp_add, Scale.b]; exact Real.exp_le_exp.2 (by linarith)
  have hXb' : s.X' ≤ s.b := (le_mul_of_one_le_left (by linarith) hX1).trans hXb
  have hb1 : 1 ≤ s.b := hX1.trans hXb'
  have hk5 : (D.R.k : ℝ) ≤ s.x ^ (5 : ℝ) := (Nat.cast_le.2 hkr).trans hr
  have hk0 : (1 : ℝ) ≤ D.R.k := by exact_mod_cast (by have := D.R.m_add_three_le_k; omega : 1 ≤ D.R.k)
  have hm0 : (1 : ℝ) ≤ D.R.m := by exact_mod_cast (by have := D.R.two_le_m; omega : 1 ≤ D.R.m)
  have hn0 : (1 : ℝ) ≤ D.R.n := (one (by linarith)).trans hn1
  have hlt : ∀ p : ℕ, p.Prime → Real.log p < u → (p : ℝ) < s.X' := fun p hp h =>
    (Real.log_lt_iff_lt_exp (by exact_mod_cast hp.pos)).1 h
  refine ⟨⟨⟨⟨hn1, hn2, ?_⟩, ⟨?_, ?_⟩, hk1, hk2⟩, ⟨?_, ?_, ?_, ?_, hn2, hk2⟩, ⟨((D.R.k : ℝ) * s.b) ^ 8, le_rfl, ?_, ?_, hg⟩,
    ⟨?_, ?_, ?_, ?_, ?_, ?_⟩⟩, ?_⟩
  · have : s.x ^ (1 : ℝ) ≤ D.R.n := (mono (by linarith)).trans hn1
    rw [Real.rpow_one] at this
    have : (4 : ℝ) ≤ D.R.n := by linarith [show (4 : ℝ) < 44 ^ 3 by norm_num]
    exact_mod_cast this
  · rw [← Real.sqrt_eq_rpow]; exact hm1'
  · rw [← Real.sqrt_eq_rpow]; exact hm2'
  · exact (mono (by linarith)).trans hm1
  · have : s.x ^ (1 / 2 : ℝ) = s.x ^ (s.eps / 16) * s.x ^ (1 / 2 - s.eps / 16) := by
      rw [← Real.rpow_add hx0]; congr 1; ring
    rw [this]
    exact hm2.trans (mul_le_mul_of_nonneg_right h16 (by positivity))
  · have h1 : s.x ^ (1 / 3 : ℝ) ≤ D.R.m := (mono (by linarith)).trans hm1
    have h2 : (44 : ℝ) ≤ s.x ^ (1 / 3 : ℝ) := by
      calc (44 : ℝ) = ((44 : ℝ) ^ 3) ^ (1 / 3 : ℝ) := by
            rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]; norm_num
        _ ≤ _ := Real.rpow_le_rpow (by positivity) h44 (by norm_num)
    exact_mod_cast h2.trans h1
  · linarith
  · have e : (((D.R.k : ℝ) * s.b) ^ 8) ^ (1 / 4 : ℝ) = ((D.R.k : ℝ) * s.b) ^ 2 := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity), ← Real.rpow_natCast]; norm_num
    have c0 : (0 : ℝ) < (LevelStarExponents.condE D : ℝ) := by
      have := hqp.pos; have := hdp.pos; have := D.host.QS_pos
      unfold LevelStarExponents.condE; push_cast; positivity
    have c1 : (LevelStarExponents.condE D : ℝ) ^ C.P.CY ≤ s.b := by
      rw [Real.rpow_def_of_pos c0]
      refine le_trans (Real.exp_le_exp.2 ?_) hXb'
      have : Real.log (LevelStarExponents.condE D : ℝ) ≤ 2 * w := by
        unfold LevelStarExponents.condE; push_cast; exact hcond'
      have := mul_le_mul_of_nonneg_right this (show 0 ≤ C.P.CY by linarith)
      linarith only [this, hA3]
    have c2 : (D.R.r : ℝ) ^ 4 ≤ s.b := by
      calc (D.R.r : ℝ) ^ 4 ≤ (s.x ^ (5 : ℝ)) ^ 4 := by gcongr
        _ = s.x ^ (20 : ℝ) := by rw [← Real.rpow_natCast, ← Real.rpow_mul hx0.le]; norm_num
        _ ≤ s.x ^ (406 : ℝ) := mono (by norm_num)
        _ ≤ s.b := by linarith [one (show (0 : ℝ) ≤ 406 by norm_num)]
    rw [e]
    calc (D.R.r : ℝ) ^ 4 * (LevelStarExponents.condE D : ℝ) ^ C.P.CY ≤ s.b * s.b := by gcongr
      _ = (1 * s.b) ^ 2 := by ring
      _ ≤ _ := by gcongr
  · have c2 : 2 * (D.R.k : ℝ) ^ 8 ≤ s.b := by
      calc 2 * (D.R.k : ℝ) ^ 8 ≤ 2 * (s.x ^ (5 : ℝ)) ^ 8 := by gcongr
        _ = 2 * s.x ^ (40 : ℝ) := by rw [← Real.rpow_natCast, ← Real.rpow_mul hx0.le]; norm_num
        _ ≤ 2 * s.x ^ (406 : ℝ) := by linarith [mono (show (40 : ℝ) ≤ 406 by norm_num)]
        _ ≤ s.b := by linarith [one (show (0 : ℝ) ≤ 406 by norm_num)]
    calc 2 * ((D.R.k : ℝ) * s.b) ^ 8 = 2 * (D.R.k : ℝ) ^ 8 * s.b ^ 8 := by ring
      _ ≤ s.b * s.b ^ 8 := by gcongr
      _ = s.b ^ 9 := by ring
  · exact hlt _ hqp (by linarith)
  · exact hlt _ hdp (by linarith)
  · exact hlt _ D.host.pde_prime hpw
  · exact hlt _ D.host.pde'_prime hpw'
  · have hb0 : 0 < s.b := by linarith
    have e : s.X'' D.R.n = s.x * D.R.n * s.X' := by
      unfold Scale.X'' Scale.w'' Scale.b' Scale.a
      field_simp
    rw [e]
    exact le_mul_of_one_le_left (by linarith) (one_le_mul_of_one_le_of_one_le hx1.le hn0)
  · have c1 := (rank_mul_le hx0 (Nat.cast_nonneg _) hf hN).trans (mono (b := 406) (by norm_num))
    linarith [one (show (0 : ℝ) ≤ 406 by norm_num)]
  · have hw'' : s.w'' D.R.n ≤ s.b := by
      have e : s.w'' D.R.n = s.b / (D.R.n * s.X') := by
        unfold Scale.w'' Scale.b' Scale.a
        field_simp
      rw [e]
      exact div_le_self (by linarith) (one_le_mul_of_one_le_of_one_le hn0 hX1)
    have ht0 : (0 : ℝ) ≤ D.R.t := Nat.cast_nonneg _
    have hS : L.Sc ≤ s.b := ((le_mul_of_one_le_left L.Sc_pos.le hk0).trans P.kS_le).trans hw''
    have hE : L.etaSz ≤ s.b :=
      ((le_mul_of_one_le_left L.etaSz_pos.le (one_le_mul_of_one_le_of_one_le hm0 (by linarith))).trans P.mteta).trans hw''
    have hh : 3 * hWidth L ≤ 15 * s.b := by
      have := P.t_le_eta
      unfold hWidth; linarith
    have hh0 : 0 < 3 * hWidth L := by
      have := L.Sc_pos; have := L.etaSz_pos
      unfold hWidth; linarith
    have hlg : Real.log (3 * hWidth L) ≤ 4 * s.L := by
      have c1 := Real.log_le_log hh0 hh
      rw [Real.log_mul (x := 15) (by norm_num) (by linarith), Scale.b, Real.log_exp] at c1
      have c2 : Real.log 15 ≤ 3 := by
        rw [Real.log_le_iff_le_exp (by norm_num), show (3 : ℝ) = 1 + 1 + 1 by norm_num, Real.exp_add, Real.exp_add]
        have := Real.exp_one_gt_d9
        have h7 : 7 ≤ Real.exp 1 * Real.exp 1 := by nlinarith only [this]
        nlinarith only [this, h7]
      linarith
    have hmt : (D.R.m : ℝ) + D.R.t ≤ 2 * s.x ^ (401 : ℝ) := by
      have := mono (show (1 : ℝ) ≤ 401 by norm_num)
      rw [Real.rpow_one] at this
      linarith
    have e : s.x ^ (406 : ℝ) = s.x ^ (5 : ℝ) * s.x ^ (401 : ℝ) := by rw [← Real.rpow_add hx0]; norm_num
    unfold lJ
    rw [le_div_iff₀ (lJ_den_pos L)]
    have hl0 : 0 ≤ Real.log (3 * hWidth L) := by
      apply Real.log_nonneg
      have := L.Sc_pos; have := L.etaSz_pos
      unfold hWidth; linarith
    calc s.X' * ((D.R.k : ℝ) * ((D.R.m : ℝ) + D.R.t) * Real.log (3 * hWidth L))
        ≤ s.X' * (s.x ^ (5 : ℝ) * (2 * s.x ^ (401 : ℝ)) * (4 * s.L)) := by gcongr
      _ = s.X' * (8 * s.x ^ (406 : ℝ)) * s.L := by rw [e]; ring
      _ ≤ s.X' * s.X' * s.L := by gcongr
      _ ≤ (1 * s.b) * s.L := by rw [one_mul]; exact mul_le_mul_of_nonneg_right hXb (by linarith)
      _ ≤ (D.R.m : ℝ) * s.b * s.L := by gcongr

end GlobalTheory.ClassDuty

end
