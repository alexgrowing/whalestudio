import Mathlib
import Formalism.SharpRestriction.Divisibility.LocalQuadraticParts
import Formalism.LocalRingCardinality.CoeNeZeroOfNotMem
open Formalism.BasicNotions Formalism.BasicNotions.DV Formalism.MainNotions NumberField IsDedekindDomain

namespace GlobalTheory

theorem rpow_le_exp_rpow_eventually {ε : ℝ} (hε : 0 < ε) (c : ℝ) :
    ∃ x0 : ℝ, ∀ x ≥ x0, x ^ c ≤ Real.exp (x ^ ε) := by
  have h := ((tendsto_exp_div_rpow_atTop (c / ε)).comp (tendsto_rpow_atTop hε)).eventually_ge_atTop 1
  obtain ⟨x0, hx0⟩ := Filter.eventually_atTop.1 (h.and (Filter.eventually_gt_atTop 0))
  refine ⟨x0, fun x hx => ?_⟩
  obtain ⟨h1, h2⟩ := hx0 x hx
  simp only [Function.comp] at h1
  rw [← Real.rpow_mul h2.le, mul_div_cancel₀ _ hε.ne', le_div_iff₀ (Real.rpow_pos_of_pos h2 _), one_mul] at h1
  exact h1

theorem poly_sizes_ranks_weights : ∀ (eps : ℝ) (Fm : FamP eps), (∃ x0 : ℝ, ∀ x ≥ x0, Fm.x1 < x → ∀ i : Fm.Ix x, 0 ≤ Fm.Ct ∧ ((Fm.D x i).R.f : ℝ) ≤ x ^ (3 : ℝ) ∧ ((Fm.D x i).R.m : ℝ) ≤ x ∧ ((Fm.D x i).R.k : ℝ) ≤ x ^ (5 : ℝ) ∧ ((Fm.D x i).R.N (Fm.D x i).R.m : ℝ) ≤ x ^ (Fm.Ct + 6) ∧ ((Fm.D x i).R.nV : ℝ) ≤ x ^ (Fm.Ct + 6) ∧ ((Fm.D x i).host.TT.card : ℝ) ≤ x ^ (3 : ℝ) ∧ (Fm.L x i).sc.x = x ∧ (Fm.L x i).sc.a = x * (Fm.L x i).sc.b ∧ 1 ≤ (Fm.L x i).sc.L ∧ (Fm.L x i).sc.L ≤ x ∧ x ^ (Fm.Ct + 6) ≤ (Fm.L x i).sc.b ∧ (∀ t, (0 : ℝ) ≤ (Fm.L x i).aT t ∧ ((Fm.L x i).aT t : ℝ) ≤ 2 * x * (Fm.L x i).sc.b) ∧ (Fm.L x i).B0 ≤ x ^ (5 : ℝ) * (Fm.L x i).sc.b ∧ 0 ≤ (Fm.L x i).B0) := by
  intro eps Fm
  have heps : 0 < eps := by
    obtain ⟨i⟩ := Fm.Ix_zero
    rw [← Fm.L_eps 0 i]; exact (Fm.L 0 i).sc.eps_pos
  obtain ⟨x0, hx0⟩ := rpow_le_exp_rpow_eventually heps (Fm.Ct + 6)
  refine ⟨max x0 4, fun x hx hx1 i => ?_⟩
  have hexp := hx0 x (le_trans (le_max_left _ _) hx)
  have hx4 : 4 ≤ x := le_trans (le_max_right _ _) hx
  have hS := Fm.sizes x hx1 i
  have hLx := Fm.L_x x i hx1
  have hLe := Fm.L_eps x i
  have hCt := Fm.Ct_eq x i
  generalize Fm.L x i = L at *
  generalize Fm.Ct = Ct at *
  obtain ⟨hN, hM, hK, -, -, -, -, hTT, -⟩ := hS
  have hlt : eps < 1 / 52 := hLe ▸ L.sc.eps_lt
  have h1x : (1 : ℝ) ≤ x := by linarith
  have h0x : (0 : ℝ) < x := by linarith
  have htw := L.t_win
  have haw := L.aT_win
  have hN2 := hN.2
  have hM2 := hM.2
  have hK2 := hK.2
  have hTT2 := hTT.2
  unfold szNst at hTT2
  unfold szTh at hN2 hM2 hK2
  unfold Scale.delta1 at hM2 hTT2
  rw [hLx, hLe] at hN2 hM2 hK2 hTT2
  rw [hLx, hCt] at htw
  have hd : x ^ (-(eps / 8)) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos h1x (by linarith)
  have hd0 : 0 < x ^ (-(eps / 8)) := Real.rpow_pos_of_pos h0x _
  have hs2 : (2 : ℝ) ≤ x ^ (1 / 2 : ℝ) := by
    rw [← Real.sqrt_eq_rpow]; exact Real.le_sqrt_of_sq_le (by linarith)
  have hfn : ((Fm.D x i).R.f : ℝ) = 2 * (Fm.D x i).R.n := by unfold Ranks.f; push_cast; ring
  have hf : ((Fm.D x i).R.f : ℝ) ≤ x ^ (3 : ℝ) := by
    have h1 : ((Fm.D x i).R.n : ℝ) ≤ x ^ (5 / 2 : ℝ) :=
      hN2.trans (Real.rpow_le_rpow_of_exponent_le h1x (by linarith))
    rw [hfn, show (3 : ℝ) = 1 / 2 + 5 / 2 by norm_num, Real.rpow_add h0x]
    exact mul_le_mul hs2 h1 (by positivity) (by positivity)
  have hm : ((Fm.D x i).R.m : ℝ) ≤ x := by
    have h1 : x ^ (eps / 100) ≤ Real.sqrt x := by
      rw [Real.sqrt_eq_rpow]; exact Real.rpow_le_rpow_of_exponent_le h1x (by linarith)
    have h2 : Real.sqrt (x * x ^ (-(eps / 8))) ≤ Real.sqrt x :=
      Real.sqrt_le_sqrt (by nlinarith)
    refine hM2.trans ((mul_le_mul h1 h2 (by positivity) (by positivity)).trans ?_)
    exact (Real.mul_self_sqrt h0x.le).le
  have hk : ((Fm.D x i).R.k : ℝ) ≤ x ^ (5 : ℝ) :=
    hK2.trans (Real.rpow_le_rpow_of_exponent_le h1x (by linarith))
  have hCt0 : 0 ≤ Ct := by
    by_contra hc
    have := Real.rpow_lt_one_of_one_lt_of_neg (show (1 : ℝ) < x by linarith) (not_le.1 hc)
    linarith [htw.1, htw.2]
  have h6 : 3 * x ≤ x ^ (6 : ℝ) := by
    have : x ^ ((2 : ℕ) : ℝ) ≤ x ^ (6 : ℝ) := Real.rpow_le_rpow_of_exponent_le h1x (by norm_num)
    rw [Real.rpow_natCast] at this
    nlinarith
  have hT0 : 0 < x ^ Ct := Real.rpow_pos_of_pos h0x _
  have hbig : 3 * x * (Fm.D x i).R.t ≤ x ^ (Ct + 6) := by
    rw [add_comm, Real.rpow_add h0x]
    exact mul_le_mul h6 htw.2 (by positivity) (by positivity)
  have hrt := (Fm.D x i).R.rank_add_five_le
  have h2m := (Fm.D x i).R.two_le_m
  have hk3 := (Fm.D x i).R.m_add_three_le_k
  have hNm : ((Fm.D x i).R.N (Fm.D x i).R.m : ℝ) ≤ x ^ (Ct + 6) := by
    have h1 : (Fm.D x i).R.N (Fm.D x i).R.m ≤ 3 * (Fm.D x i).R.m * (Fm.D x i).R.t := by
      unfold Ranks.N
      have a1 : (Fm.D x i).R.k ≤ (Fm.D x i).R.t := by omega
      have a2 : 1 ≤ (Fm.D x i).R.t := by omega
      nlinarith
    have h2 : ((Fm.D x i).R.N (Fm.D x i).R.m : ℝ) ≤ 3 * (Fm.D x i).R.m * (Fm.D x i).R.t := by exact_mod_cast h1
    refine h2.trans (le_trans ?_ hbig)
    gcongr
  have hnV : ((Fm.D x i).R.nV : ℝ) ≤ x ^ (Ct + 6) := by
    have h1 : (Fm.D x i).R.nV ≤ 2 * (Fm.D x i).R.t := by
      unfold Ranks.nV Ranks.r; omega
    have h2 : ((Fm.D x i).R.nV : ℝ) ≤ 2 * (Fm.D x i).R.t := by exact_mod_cast h1
    refine h2.trans (le_trans ?_ hbig)
    have := htw.1
    nlinarith
  have hTTc : ((Fm.D x i).host.TT.card : ℝ) ≤ x ^ (3 : ℝ) := by
    refine hTT2.trans (le_trans ?_ hf)
    rw [hfn]
    exact mul_le_of_le_one_right (by positivity) hd
  have ha : L.sc.a = x * L.sc.b := by unfold Scale.a; rw [hLx]
  have hL : L.sc.L = x ^ eps := by unfold Scale.L; rw [hLx, hLe]
  have hL1 : 1 ≤ L.sc.L := by rw [hL]; exact Real.one_le_rpow h1x heps.le
  have hL2 : L.sc.L ≤ x := by
    rw [hL]
    calc x ^ eps ≤ x ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le h1x (by linarith)
      _ = x := Real.rpow_one x
  have hb : L.sc.b = Real.exp (x ^ eps) := by unfold Scale.b; rw [hL]
  have hb0 : 0 < L.sc.b := by rw [hb]; positivity
  have hB0 : L.B0 = (Fm.D x i).R.f * (Fm.D x i).R.m * L.sc.b * L.sc.L := by
    unfold SizeData₂.B0 sizeBudget bSize
    rw [hb, hL, hLx, hLe]
  refine ⟨hCt0, hf, hm, hk, hNm, hnV, hTTc, hLx, ha, hL1, hL2, hb ▸ hexp, fun t => ?_, ?_, ?_⟩
  · obtain ⟨h1, h2⟩ := haw t
    have ha0 : 0 < L.sc.a := by rw [ha]; positivity
    have hk1 : (1 : ℝ) ≤ (Fm.D x i).R.k := by
      have : 1 ≤ (Fm.D x i).R.k := by omega
      exact_mod_cast this
    have hA : 1 ≤ L.sc.x ^ (Scale.A / 2) := Real.one_le_rpow L.sc.one_lt_alt.le (by unfold Scale.A; norm_num)
    have h3 := div_le_self ha0.le (one_le_mul_of_one_le_of_one_le hk1 hA)
    refine ⟨by linarith, ?_⟩
    rw [mul_assoc, ← ha]; linarith
  · rw [hB0, show (5 : ℝ) = 3 + 1 + 1 by norm_num, Real.rpow_add h0x, Real.rpow_add h0x, Real.rpow_one]
    calc ((Fm.D x i).R.f : ℝ) * (Fm.D x i).R.m * L.sc.b * L.sc.L ≤ x ^ (3 : ℝ) * x * L.sc.b * x := by
          gcongr
      _ = _ := by ring
  · rw [hB0]; positivity

end GlobalTheory
