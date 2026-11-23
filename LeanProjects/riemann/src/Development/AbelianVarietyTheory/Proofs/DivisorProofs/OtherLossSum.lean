import Mathlib
import Formalism.SharpRestriction.Divisibility.LocalQuadraticParts
import Formalism.SharpRestriction.GrowthBounds.WeilJacquetShalikaLaw
import Formalism.SharpRestriction.GlobalSchurBounds.MainIn
import Formalism.QuotientMetricDivisors.FinalW
import Formalism.QuotientMetricDivisors.SixthReductionExplicit
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.FrameFacts
import Development.AutomorphicArithmetic.OrbitLabellings.TwoPowDvdSubOrAddOneOfOddAddOrderOfHP
import Development.AutomorphicArithmetic.OrbitLabellings.SumLogDivCubeLeOfTwoPowDvd

open Formalism.BasicNotions Formalism.BasicNotions.DV Formalism.MainNotions NumberField Classical

noncomputable section

namespace GlobalTheory.OtherLoss

open Formalism.MainNotions.G

theorem nums {D : D7} {L : SizeData₂ D} (h : SizesAt L) :
    (D.R.k : ℝ) * (L.sc.b' + L.etaSz) ≤ D.R.m * L.sc.b ∧ L.Sc ≤ L.sc.b ∧ L.sc.b' ≤ L.sc.b ∧
    L.sc.X'' D.R.n * L.etaSz ≤ L.sc.b ∧ Nm D ^ 2 ≤ L.etaSz ∧ 4 * Nm D ≤ L.etaSz ∧ L.sc.L ≤ L.etaSz ∧
    (D.R.f : ℝ) * L.etaSz ≤ L.sc.b ∧ 2 * L.sc.x ≤ L.sc.b ∧ (∀ t, (L.bT t : ℝ) ≤ 2 * L.sc.b') ∧
    L.sc.w'' D.R.n ≤ L.sc.b' ∧ 0 < L.sc.w'' D.R.n := by
  obtain ⟨-, -, -, -, -, -, -, -, hLa, hRho, hBot, -, -, hEta, hNodes, hLs, -⟩ := h
  have hx1 := L.sc.one_lt_alt
  have hx : 0 < L.sc.x := lt_trans one_pos hx1
  have hb : 0 < L.sc.b := Real.exp_pos _
  have hb' : 0 < L.sc.b' := div_pos (mul_pos hx hb) (Real.exp_pos _)
  have hL : 1 ≤ L.sc.L := Real.one_le_rpow L.sc.one_lt_alt.le L.sc.eps_pos.le
  have hmn := D.R.two_le_m
  have hkn := D.R.m_add_three_le_k
  have hmfn : D.R.m ≤ D.R.f := D.R.m_le_f
  have hm : (1 : ℝ) ≤ D.R.m := by exact_mod_cast (by omega : 1 ≤ D.R.m)
  have hk : (1 : ℝ) ≤ D.R.k := by exact_mod_cast (by omega : 1 ≤ D.R.k)
  have hmk : (D.R.m : ℝ) ≤ D.R.k := by exact_mod_cast (by omega : D.R.m ≤ D.R.k)
  have hf : (1 : ℝ) ≤ D.R.f := by exact_mod_cast (by omega : 1 ≤ D.R.f)
  have hn : (1 : ℝ) ≤ D.R.n := by exact_mod_cast D.R.ord_pos
  have ht : (1 : ℝ) ≤ D.R.t := L.t_win.1
  have hN : (1 : ℝ) ≤ D.R.N D.R.m := by
    exact_mod_cast (by unfold Ranks.N; omega : 1 ≤ D.R.N D.R.m)
  have hη := L.etaSz_pos
  have hS := L.Sc_pos
  have hηm : L.etaSz / D.R.m ≤ L.etaSz := div_le_self hη.le hm

  have hden : (D.R.k : ℝ) ≤ (D.R.n : ℝ) * (D.R.t : ℝ) ^ 2 * ((D.R.N D.R.m : ℝ) + D.R.t) * L.sc.L ^ 2 +
      (D.R.k : ℝ) * (D.R.n : ℝ) ^ 2 * (L.Sc + D.R.t + L.sc.L) := by
    have a1 : 0 ≤ (D.R.n : ℝ) * (D.R.t : ℝ) ^ 2 * ((D.R.N D.R.m : ℝ) + D.R.t) * L.sc.L ^ 2 := by positivity
    have a2 : (1 : ℝ) ≤ (D.R.n : ℝ) ^ 2 * (L.Sc + D.R.t + L.sc.L) :=
      one_le_mul_of_one_le_of_one_le (one_le_pow₀ hn) (by linarith)
    have a3 := le_mul_of_one_le_right (by linarith : (0 : ℝ) ≤ D.R.k) a2
    rw [← mul_assoc] at a3
    linarith
  have hl1 : szlStar L ≤ D.R.m * L.sc.b / D.R.k :=
    div_le_div_of_nonneg_left (by positivity) (by linarith) hden
  have hl0 : 0 ≤ szlStar L := div_nonneg (by positivity) (by linarith)
  have hl2 : L.sc.b' + L.Sc + L.etaSz ≤ D.R.m * L.sc.b / D.R.k := by
    have := hLs.1
    have a : 0 ≤ L.sc.b / szlStar L := div_nonneg hb.le hl0
    linarith
  have hl3 : (D.R.m : ℝ) * L.sc.b / D.R.k ≤ L.sc.b := by
    rw [div_le_iff₀ (by linarith)]
    nlinarith
  have hw : L.sc.w'' D.R.n ≤ L.sc.b' :=
    div_le_self hb'.le (one_le_mul_of_one_le_of_one_le hx1.le hn)
  have hw0 : 0 < L.sc.w'' D.R.n := div_pos hb' (by positivity)
  have hxη : L.sc.x * L.etaSz ≤ L.sc.w'' D.R.n := by
    have a := hEta.2.2.2.1
    rw [le_div_iff₀ hx] at a
    have a2 : L.etaSz ≤ D.R.t * L.etaSz := le_mul_of_one_le_left hη.le ht
    nlinarith
  have hN3 : 4 * (D.R.N D.R.m : ℝ) ^ 3 + 6 ≤ L.etaSz := by
    have := hNodes.2.2.2.1
    linarith
  have a3 : (D.R.N D.R.m : ℝ) ^ 2 ≤ (D.R.N D.R.m : ℝ) ^ 3 := pow_le_pow_right₀ hN (by norm_num)
  have a4 : (D.R.N D.R.m : ℝ) ^ 1 ≤ (D.R.N D.R.m : ℝ) ^ 3 := pow_le_pow_right₀ hN (by norm_num)
  rw [pow_one] at a4
  refine ⟨?_, by linarith, by linarith, ?_, by unfold Nm; linarith, by unfold Nm; linarith, ?_, ?_, ?_, ?_, hw, hw0⟩
  · rw [le_div_iff₀ (by linarith)] at hl2
    nlinarith
  · unfold Scale.X'' Scale.a
    rw [div_mul_eq_mul_div, div_le_iff₀ hw0]
    nlinarith
  · have a := hNodes.2.1
    have a2 : L.sc.L ≤ D.R.k * D.R.t * L.sc.L :=
      le_mul_of_one_le_left (by linarith) (one_le_mul_of_one_le_of_one_le hk ht)
    linarith
  · have a1 := hEta.2.1
    rw [le_div_iff₀ (by positivity)] at a1
    have a2 : (1 : ℝ) ≤ (D.R.t : ℝ) ^ 3 * (D.R.k : ℝ) ^ 3 :=
      one_le_mul_of_one_le_of_one_le (one_le_pow₀ ht) (one_le_pow₀ hk)
    have a3 : (D.R.f : ℝ) * L.etaSz ≤ (D.R.f : ℝ) * L.etaSz * ((D.R.t : ℝ) ^ 3 * (D.R.k : ℝ) ^ 3) :=
      le_mul_of_one_le_right (by positivity) a2
    calc _ ≤ _ := a3
      _ = L.etaSz * ((D.R.t : ℝ) ^ 3 * D.R.f * (D.R.k : ℝ) ^ 3) := by ring
      _ ≤ _ := a1
  · have : L.sc.x * 2 ≤ L.sc.x * L.etaSz := mul_le_mul_of_nonneg_left (by nlinarith) hx.le
    linarith
  · intro t
    have hLa0 : 0 ≤ L.LaG := le_trans (by positivity) hLa.1
    have hx2 : L.sc.x ^ (-2 : ℝ) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hx1.le (by norm_num)
    have h5 : 0 ≤ L.sc.x ^ szTh L * Real.log L.sc.x * L.LaG / D.R.k :=
      div_nonneg (mul_nonneg (mul_nonneg (by positivity) (Real.log_nonneg hx1.le)) hLa0) (by linarith)
    unfold SizeRho at hRho
    have h6 : szNst L * L.sc.x ^ L.sc.eps * L.LaG / D.R.k ≤ 1 / 4 := by
      have : 4 * szNst L * L.sc.x ^ L.sc.eps * L.LaG / D.R.k =
        4 * (szNst L * L.sc.x ^ L.sc.eps * L.LaG / D.R.k) := by ring
      linarith
    have h7 := hBot t
    have h8 : szNst L * L.sc.x ^ L.sc.eps * L.LaG * L.sc.b' / D.R.k =
      (szNst L * L.sc.x ^ L.sc.eps * L.LaG / D.R.k) * L.sc.b' := by ring
    have h9 := mul_le_mul_of_nonneg_right h6 hb'.le
    linarith

theorem wPl_bounds {D : D7} {L : SizeData₂ D} (h : SizesAt L) {j : ℕ} (hj : j ∈ SizeData₂.lifts D) (z : Bool × HH D) :
    0 ≤ wPl D j z ∧ wPl D j z ≤ 9 * L.sc.b ∧ (z.1 = false → wPl D j z ≤ 3 * (L.sc.b' + L.etaSz)) := by
  obtain ⟨-, -, hb'b, -, -, -, -, hfη, h2x, hbT, hw, hw0⟩ := nums h
  obtain ⟨hj1, hj2⟩ := Finset.mem_Icc.1 hj
  have hx1 := L.sc.one_lt_alt
  have hx : 0 < L.sc.x := lt_trans one_pos hx1
  have hb : 0 < L.sc.b := Real.exp_pos _
  have hb' : 0 < L.sc.b' := div_pos (mul_pos hx hb) (Real.exp_pos _)
  have hmn := D.R.two_le_m
  have hmfn : D.R.m ≤ D.R.f := D.R.m_le_f
  have hf : (1 : ℝ) ≤ D.R.f := by exact_mod_cast (by omega : 1 ≤ D.R.f)
  have hη := L.etaSz_pos
  have hηb : L.etaSz ≤ L.sc.b := (le_mul_of_one_le_left hη.le hf).trans hfη
  have hq : L.sc.b' / L.sc.x ≤ L.sc.b' := div_le_self hb'.le hx1.le
  have hq0 : 0 < L.sc.b' / L.sc.x := div_pos hb' hx
  unfold wPl
  by_cases h1 : (D.eTau (tauPl D z) : D.R.GG) ∈ D.host.thickPlaces
  · obtain ⟨a1, a2⟩ := L.win_thick j hj1 hj2 _ h1
    refine ⟨by linarith, by linarith, fun hz => ?_⟩
    exfalso
    obtain ⟨s, -, e⟩ := Finset.mem_image.mp h1
    unfold tauPl at e
    rw [Equiv.apply_symm_apply] at e
    have e2 := congrArg (fun g : D.R.GG => g.1.1) e
    simp [plGG, hz, Formalism.HC.Frame.tau1, Formalism.HC.Frame.tau2] at e2
  by_cases h2 : (D.eTau (tauPl D z) : D.R.GG) ∈ D.host.topPlaces
  · obtain ⟨t, ht, e⟩ := Finset.mem_image.mp h2
    obtain ⟨a1, a2⟩ := L.win_top j hj1 hj2 _ ⟨t, ht⟩ e.symm
    have a3 := L.bT_ge ⟨t, ht⟩
    have a4 := hbT ⟨t, ht⟩
    exact ⟨by linarith, by linarith, fun _ => by linarith⟩
  · obtain ⟨a1, a2⟩ := L.win_thin j hj1 hj2 _ ⟨(D.eTau _).2, h2, h1⟩
    exact ⟨by linarith, by linarith, fun _ => by linarith⟩

theorem card_places (D : D7) : Fintype.card (Bool × HH D) = D.R.f := by
  rw [Fintype.card_prod, Fintype.card_bool, D.R.card_A]
  rfl

theorem card_le_f (D : D7) (s : Finset (Bool × HH D)) : (s.card : ℝ) ≤ D.R.f := by
  exact_mod_cast (Finset.card_le_univ s).trans (card_places D).le

theorem nP_le_f (D : D7) (p : ℕ) : nP D p ≤ D.R.f := by
  have h : ∀ y : HH D, addOrderOf y ≤ D.R.n := fun y => by
    have := addOrderOf_le_card_univ (x := y)
    rwa [D.R.card_A] at this
  unfold nP Ranks.f
  split
  · exact Nat.mul_le_mul_left 2 (h _)
  · have := h (hP D p)
    omega

theorem gam_bounds {p : ℕ} (hp : 2 ≤ p) : 0 ≤ gam p ∧ gam p ≤ 2 / p := by
  have h : (2 : ℝ) ≤ p := by exact_mod_cast hp
  have h1 : (0 : ℝ) < (p : ℝ) ^ 2 - 1 := by nlinarith
  unfold gam
  refine ⟨by positivity, ?_⟩
  rw [div_le_div_iff₀ h1 (by linarith)]
  nlinarith

theorem first_term {D : D7} {L : SizeData₂ D} (h : SizesAt L) {j : ℕ} (hj : j ∈ SizeData₂.lifts D) {p : ℕ} (hp : 2 ≤ p) :
    max 0 ((∑ z ∈ kindA D p, FOrb D j p z) / (nP D p : ℝ)) ≤ 6 * (D.R.f * D.R.m * L.sc.b) / p := by
  have hb : 0 < L.sc.b := Real.exp_pos _
  have hp' : (0 : ℝ) < p := by exact_mod_cast (by omega : 0 < p)
  have hnP : (0 : ℝ) < nP D p := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne _)
  have hkn := D.R.m_add_three_le_k
  have hk : (1 : ℝ) ≤ D.R.k := by exact_mod_cast (by omega : 1 ≤ D.R.k)
  obtain ⟨g0, g1⟩ := gam_bounds hp
  refine max_le (by positivity) ?_
  have key : ∀ z ∈ kindA D p, FOrb D j p z ≤ 6 * (D.R.m * L.sc.b) / p * nP D p := by
    intro z hz
    obtain ⟨-, hs, hz1⟩ := Finset.mem_filter.1 hz
    have a := (factLpF p (nP D p) (fun s => ((D.R.k : ℝ) - 1) * wPl D j (posPl D p z s.val)) hp
      (fun s => mul_nonneg (by linarith) (wPl_bounds h hj _).1)).2
    refine a.trans ?_
    have b : ∑ s : ZMod (nP D p), ((D.R.k : ℝ) - 1) * wPl D j (posPl D p z s.val) ≤
        ∑ _s : ZMod (nP D p), 3 * (D.R.m * L.sc.b) := by
      refine Finset.sum_le_sum fun s _ => ?_
      obtain ⟨c0, -, c1⟩ := wPl_bounds h hj (posPl D p z s.val)
      have c2 := c1 (by simp [posPl, partner, hs, hz1])
      have c3 := (nums h).1
      nlinarith
    rw [Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul] at b
    calc _ ≤ gam p * ((nP D p : ℝ) * (3 * (D.R.m * L.sc.b))) := mul_le_mul_of_nonneg_left b g0
      _ ≤ 2 / p * ((nP D p : ℝ) * (3 * (D.R.m * L.sc.b))) := mul_le_mul_of_nonneg_right g1 (by positivity)
      _ = _ := by ring
  rw [div_le_iff₀ hnP]
  refine (Finset.sum_le_card_nsmul _ _ _ key).trans ?_
  rw [nsmul_eq_mul]
  calc _ ≤ (D.R.f : ℝ) * (6 * (D.R.m * L.sc.b) / p * nP D p) :=
        mul_le_mul_of_nonneg_right (card_le_f D _) (by positivity)
    _ = _ := by ring

set_option maxHeartbeats 800000 in

theorem eatI_bound {D : D7} {L : SizeData₂ D} (h : SizesAt L) {K : Consts} {c : ErrC} (h1 : K.dl1 = 5) (h2 : K.dl2 = 4)
    (h3 : c.c6 = 12) {j : ℕ} (hj : j ∈ SizeData₂.lifts D) {p : ℕ} (hp : 2 ≤ p) (hpb : (p : ℝ) ≤ L.sc.b) :
    |EatI L K c j p - EatX L c j p| * Real.log p ≤
      126 * (D.R.f * D.R.m * L.sc.b) * (Real.log p / p) + 46 * (D.R.f * L.etaSz * L.sc.L) := by
  obtain ⟨-, hSb, -, -, hN2, hN4, hLη, hfη, h2x, -⟩ := nums h
  obtain ⟨hj1, hj2⟩ := Finset.mem_Icc.1 hj
  have hx1 := L.sc.one_lt_alt
  have hb : 0 < L.sc.b := Real.exp_pos _
  have hL : 1 ≤ L.sc.L := Real.one_le_rpow L.sc.one_lt_alt.le L.sc.eps_pos.le
  have hmn := D.R.two_le_m
  have hkn := D.R.m_add_three_le_k
  have hmfn : D.R.m ≤ D.R.f := D.R.m_le_f
  have hm : (1 : ℝ) ≤ D.R.m := by exact_mod_cast (by omega : 1 ≤ D.R.m)
  have hf : (1 : ℝ) ≤ D.R.f := by exact_mod_cast (by omega : 1 ≤ D.R.f)
  have hN : (1 : ℝ) ≤ Nm D := by
    unfold Nm
    exact_mod_cast (by unfold Ranks.N; omega : 1 ≤ D.R.N D.R.m)
  have hη := L.etaSz_pos
  have hS := L.Sc_pos
  have hηb : L.etaSz ≤ L.sc.b := (le_mul_of_one_le_left hη.le hf).trans hfη
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp
  have hp0 : (0 : ℝ) < p := by linarith
  have hl2 : 1 / 2 ≤ Real.log p := by
    have := Real.log_two_gt_d9
    have := Real.log_le_log (by norm_num) hp2
    linarith
  have hl0 : 0 < Real.log p := by linarith
  have hlogb : Real.log L.sc.b = L.sc.L := Real.log_exp _
  have hlL : Real.log p ≤ L.sc.L := hlogb ▸ Real.log_le_log hp0 hpb
  obtain ⟨g0, g1⟩ := gam_bounds hp
  have hfb : D.R.f * L.sc.b ≤ D.R.f * D.R.m * L.sc.b := by
    have := mul_le_mul_of_nonneg_left hm (by positivity : (0 : ℝ) ≤ D.R.f * L.sc.b)
    linarith
  have ha1 : 1 ≤ L.sc.a := one_le_mul_of_one_le_of_one_le hx1.le (by linarith)
  have ha2 : 2 * L.sc.a ≤ L.sc.b ^ 2 := by
    unfold Scale.a
    have := mul_le_mul_of_nonneg_right h2x hb.le
    linarith only [this]
  have la0 : 0 ≤ Real.log (2 * L.sc.a) := Real.log_nonneg (by linarith)
  have la1 : Real.log (2 * L.sc.a) ≤ 2 * L.sc.L := by
    have := Real.log_le_log (by linarith) ha2
    rw [Real.log_pow, hlogb] at this
    exact_mod_cast this
  have hnP1 : (1 : ℝ) ≤ nP D p := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne _)
  have hnP2 : (nP D p : ℝ) ≤ D.R.f := by exact_mod_cast nP_le_f D p
  have hq1 : 1 ≤ 4 * (nP D p : ℝ) * Nm D * L.sc.a :=
    one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le (by linarith) hN) ha1
  have lq0 : 0 ≤ Real.log (4 * (nP D p : ℝ) * Nm D * L.sc.a) := Real.log_nonneg hq1
  have lq1 : Real.log (4 * (nP D p : ℝ) * Nm D * L.sc.a) ≤ 3 * L.sc.L := by
    have a1 : (nP D p : ℝ) * (4 * Nm D) ≤ D.R.f * L.etaSz := mul_le_mul hnP2 hN4 (by linarith) (by linarith)
    have a2 : (nP D p : ℝ) * (4 * Nm D) * L.sc.a ≤ L.sc.b * L.sc.b ^ 2 :=
      mul_le_mul (a1.trans hfη) (by linarith) (by linarith) hb.le
    have a3 : 4 * (nP D p : ℝ) * Nm D * L.sc.a ≤ L.sc.b ^ 3 := by linarith
    have := Real.log_le_log (by linarith) a3
    rw [Real.log_pow, hlogb] at this
    exact_mod_cast this
  have cT := card_le_f D (topsBC D p)
  have cK := card_le_f D (kindBC D p)
  have hNN : (D.R.N (j - 1) : ℝ) * (D.R.N j : ℝ) ≤ L.etaSz := by
    have mono : ∀ i, i ≤ D.R.m → (D.R.N i : ℝ) ≤ Nm D := fun i hi => by
      unfold Nm Ranks.N
      exact_mod_cast Nat.add_le_add_left (Nat.mul_le_mul_right _ hi) _
    have := mul_le_mul (mono (j - 1) (by omega)) (mono j hj2) (Nat.cast_nonneg _) (by linarith)
    linarith only [this, hN2]
  have t1 := first_term h hj hp
  have t2 : gam p * ((topsBC D p).card : ℝ) * (L.sc.b + L.etaSz + 1 + 3 * L.Sc) ≤
      12 * (D.R.f * D.R.m * L.sc.b) / p := by
    calc _ ≤ 2 / p * D.R.f * (6 * L.sc.b) :=
          mul_le_mul (mul_le_mul g1 cT (Nat.cast_nonneg _) (by positivity)) (by linarith) (by linarith) (by positivity)
      _ = 12 * (D.R.f * L.sc.b) / p := by ring
      _ ≤ _ := div_le_div_of_nonneg_right (by linarith) hp0.le
  have s0 : 0 ≤ ∑ z ∈ kindBC D p, wPl D j z := Finset.sum_nonneg fun z _ => (wPl_bounds h hj z).1
  have t3 : 12 * (∑ z ∈ kindBC D p, wPl D j z) / (p : ℝ) ≤ 108 * (D.R.f * D.R.m * L.sc.b) / p := by
    refine div_le_div_of_nonneg_right ?_ hp0.le
    have a := Finset.sum_le_card_nsmul _ _ _ (fun z (_ : z ∈ kindBC D p) => (wPl_bounds h hj z).2.1)
    rw [nsmul_eq_mul] at a
    have a2 := mul_le_mul_of_nonneg_right cK (by positivity : 0 ≤ 9 * L.sc.b)
    linarith
  have t4 : ((kindBC D p).card : ℝ) * (D.R.N (j - 1) : ℝ) * (D.R.N j : ℝ) *
      (Real.logb p (4 * (nP D p : ℝ) * Nm D * L.sc.a) + 1) * Real.log p ≤ 4 * (D.R.f * L.etaSz * L.sc.L) := by
    have e : ((kindBC D p).card : ℝ) * (D.R.N (j - 1) : ℝ) * (D.R.N j : ℝ) *
      (Real.logb p (4 * (nP D p : ℝ) * Nm D * L.sc.a) + 1) * Real.log p =
      ((kindBC D p).card : ℝ) * ((D.R.N (j - 1) : ℝ) * (D.R.N j : ℝ)) *
      (Real.log (4 * (nP D p : ℝ) * Nm D * L.sc.a) + Real.log p) := by
      unfold Real.logb
      field_simp
    rw [e]
    calc _ ≤ D.R.f * L.etaSz * (4 * L.sc.L) :=
          mul_le_mul (mul_le_mul cK hNN (by positivity) (by positivity)) (by linarith) (by linarith) (by positivity)
      _ = _ := by ring
  have t5 : 5 * ((kindBC D p).card : ℝ) * Nm D ^ 2 * Real.logb p (2 * L.sc.a) * Real.log p ≤
      10 * (D.R.f * L.etaSz * L.sc.L) := by
    have e : 5 * ((kindBC D p).card : ℝ) * Nm D ^ 2 * Real.logb p (2 * L.sc.a) * Real.log p =
        5 * (((kindBC D p).card : ℝ) * Nm D ^ 2 * Real.log (2 * L.sc.a)) := by
      unfold Real.logb
      field_simp
    rw [e]
    have : ((kindBC D p).card : ℝ) * Nm D ^ 2 * Real.log (2 * L.sc.a) ≤ D.R.f * L.etaSz * (2 * L.sc.L) :=
      mul_le_mul (mul_le_mul cK hN2 (by positivity) (by positivity)) la1 la0 (by positivity)
    linarith
  have t6 : 4 * ((topsBC D p).card : ℝ) * Real.logb p (2 * L.sc.a) ^ 2 * Real.log p ≤
      32 * (D.R.f * L.etaSz * L.sc.L) := by
    have e : 4 * ((topsBC D p).card : ℝ) * Real.logb p (2 * L.sc.a) ^ 2 * Real.log p =
        4 * (((topsBC D p).card : ℝ) * (Real.log (2 * L.sc.a) / Real.log p) * Real.log (2 * L.sc.a)) := by
      unfold Real.logb
      field_simp
    rw [e]
    have a : Real.log (2 * L.sc.a) / Real.log p ≤ 4 * L.etaSz := by
      rw [div_le_iff₀ hl0]
      have := mul_le_mul_of_nonneg_left hl2 (by positivity : 0 ≤ 4 * L.etaSz)
      linarith only [this, la1, hLη]
    have : ((topsBC D p).card : ℝ) * (Real.log (2 * L.sc.a) / Real.log p) * Real.log (2 * L.sc.a) ≤
        D.R.f * (4 * L.etaSz) * (2 * L.sc.L) :=
      mul_le_mul (mul_le_mul cT a (by positivity) (by positivity)) la1 la0 (by positivity)
    linarith
  have lb1 : 0 ≤ Real.logb p (2 * L.sc.a) := div_nonneg la0 hl0.le
  have lb2 : 0 ≤ Real.logb p (4 * (nP D p : ℝ) * Nm D * L.sc.a) := div_nonneg lq0 hl0.le
  have m0 : 0 ≤ max 0 ((∑ z ∈ kindA D p, FOrb D j p z) / (nP D p : ℝ)) := le_max_left _ _
  have u1 := mul_le_mul_of_nonneg_right (add_le_add (add_le_add t1 t2) t3) hl0.le
  have e : (6 * (D.R.f * D.R.m * L.sc.b) / p + 12 * (D.R.f * D.R.m * L.sc.b) / p +
      108 * (D.R.f * D.R.m * L.sc.b) / p) * Real.log p = 126 * (D.R.f * D.R.m * L.sc.b) * (Real.log p / p) := by ring
  rw [e] at u1
  unfold EatI
  rw [add_sub_cancel_right, h1, h2, h3, abs_of_nonneg (by positivity)]
  linarith only [u1, t4, t5, t6]

private theorem cube_real (x k n : ℝ) (hx : 1 ≤ x) (hk : k ≤ x ^ 5) (hn : x ^ 2 ≤ n) :
    k * (Real.log n / n ^ 3) ≤ 2 := by
  have hx0 : 0 < x := by linarith
  have hn1 : 1 ≤ n := (one_le_pow₀ hx).trans hn
  set s := Real.sqrt n with hs
  have hss : n = s ^ 2 := (Real.sq_sqrt (by linarith)).symm
  have hxs : x ≤ s := Real.le_sqrt_of_sq_le hn
  have hs0 : 0 < s := by linarith
  have hl : Real.log n ≤ 2 * s := by
    rw [hss, Real.log_pow]
    have := Real.log_le_sub_one_of_pos hs0
    push_cast
    linarith
  have hl0 : 0 ≤ Real.log n := Real.log_nonneg hn1
  have hk' : k ≤ s ^ 5 := hk.trans (pow_le_pow_left₀ hx0.le hxs 5)
  calc k * (Real.log n / n ^ 3) ≤ s ^ 5 * (2 * s / n ^ 3) := by gcongr
    _ = 2 := by rw [hss]; field_simp

private theorem cube_sizes {D : D7} {L : SizeData₂ D} (hSz : SizesAt L) :
    (D.R.k : ℝ) * (Real.log ((2 : ℝ) ^ D.R.e) / ((2 : ℝ) ^ D.R.e) ^ 3) ≤ 2 := by
  obtain ⟨hN, -, hK, -⟩ := hSz
  have hx1 : 1 < L.sc.x := L.sc.one_lt_alt
  have hx0 : 0 < L.sc.x := by linarith
  have he := L.sc.eps_pos
  have he' := L.sc.eps_lt
  have hk : (D.R.k : ℝ) ≤ L.sc.x ^ 5 := by
    refine hK.2.trans ?_
    rw [← Real.rpow_natCast]
    refine Real.rpow_le_rpow_of_exponent_le hx1.le ?_
    unfold Formalism.MainNotions.szTh
    push_cast
    linarith
  have h1 : (D.R.n : ℝ) ≤ (D.R.o : ℝ) * (2 : ℝ) ^ D.R.e := by
    exact_mod_cast D.R.toFrame.ord_le_o_mul_two_pow
  have h2 : L.sc.x ^ (L.sc.eps / 100) * L.sc.x ^ 2 ≤ (D.R.n : ℝ) := by
    refine le_trans ?_ hN.1
    rw [← Real.rpow_natCast, ← Real.rpow_add hx0]
    refine Real.rpow_le_rpow_of_exponent_le hx1.le ?_
    unfold Formalism.MainNotions.szTh
    push_cast
    linarith
  have h3 : (D.R.o : ℝ) * (2 : ℝ) ^ D.R.e ≤ L.sc.x ^ (L.sc.eps / 100) * (2 : ℝ) ^ D.R.e :=
    mul_le_mul_of_nonneg_right L.o_tie (by positivity)
  have hn : L.sc.x ^ 2 ≤ (2 : ℝ) ^ D.R.e :=
    le_of_mul_le_mul_left (h2.trans (h1.trans h3)) (Real.rpow_pos_of_pos hx0 _)
  exact cube_real _ _ _ hx1.le hk hn

theorem eatX_bound {D : D7} {L : SizeData₂ D} (h : SizesAt L) {c : ErrC}
    (h3 : c.c6 = 12) {j : ℕ} (hj : j ∈ SizeData₂.lifts D) {p : ℕ} (hp : 2 ≤ p) :
    |EatX L c j p| * Real.log p ≤
      9 * (D.R.f * L.sc.b) * (D.R.k * if IsCs D p then Real.log p / (p : ℝ) ^ 3 else 0) +
        24 * (D.R.f * L.etaSz * L.sc.L) := by
  obtain ⟨-, -, -, -, hN2, -, -, -, h2x, -⟩ := nums h
  have hx1 := L.sc.one_lt_alt
  have hb : 0 < L.sc.b := Real.exp_pos _
  have hL : 1 ≤ L.sc.L := Real.one_le_rpow L.sc.one_lt_alt.le L.sc.eps_pos.le
  have hη := L.etaSz_pos
  have hkn := D.R.m_add_three_le_k
  have hk : (1 : ℝ) ≤ D.R.k := by exact_mod_cast (by omega : 1 ≤ D.R.k)
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp
  have hp0 : (0 : ℝ) < p := by linarith
  have hl0 : 0 < Real.log p := Real.log_pos (by linarith)
  have hlogb : Real.log L.sc.b = L.sc.L := Real.log_exp _
  have ha1 : 1 ≤ L.sc.a := one_le_mul_of_one_le_of_one_le hx1.le (by linarith)
  have ha2 : L.sc.a ≤ L.sc.b ^ 2 := by
    have := mul_le_mul_of_nonneg_right h2x hb.le
    unfold Scale.a at ha1 ⊢
    linarith only [this, ha1]
  have la0 : 0 ≤ Real.log L.sc.a := Real.log_nonneg ha1
  have la1 : Real.log L.sc.a ≤ 2 * L.sc.L := by
    have := Real.log_le_log (by linarith) ha2
    rw [Real.log_pow, hlogb] at this
    exact_mod_cast this
  unfold EatX
  split_ifs with hc
  swap
  · simp only [abs_zero, zero_mul, mul_zero, zero_add]
    positivity
  have s0 : 0 ≤ ∑ z ∈ kindBC D p, wPl D j z := Finset.sum_nonneg fun z _ => (wPl_bounds h hj z).1
  have s1 : ∑ z ∈ kindBC D p, wPl D j z ≤ 9 * (D.R.f * L.sc.b) := by
    have a := Finset.sum_le_card_nsmul _ _ _ (fun z (_ : z ∈ kindBC D p) => (wPl_bounds h hj z).2.1)
    rw [nsmul_eq_mul] at a
    have a2 := mul_le_mul_of_nonneg_right (card_le_f D (kindBC D p)) (by positivity : 0 ≤ 9 * L.sc.b)
    linarith
  have hk1 : (0 : ℝ) ≤ D.R.k - 1 := by linarith
  have lb : 0 ≤ Real.logb p L.sc.a := div_nonneg la0 hl0.le
  rw [h3, abs_of_nonneg (by positivity), add_mul]
  refine add_le_add ?_ ?_
  · have a : ((D.R.k : ℝ) - 1) * ∑ z ∈ kindBC D p, wPl D j z ≤ D.R.k * (9 * (D.R.f * L.sc.b)) :=
      mul_le_mul (by linarith) s1 s0 (by linarith)
    calc _ = (((D.R.k : ℝ) - 1) * ∑ z ∈ kindBC D p, wPl D j z) * (Real.log p / (p : ℝ) ^ 3) := by ring
      _ ≤ D.R.k * (9 * (D.R.f * L.sc.b)) * (Real.log p / (p : ℝ) ^ 3) :=
          mul_le_mul_of_nonneg_right a (by positivity)
      _ = _ := by ring
  · have e : 12 * (D.R.f : ℝ) * Nm D ^ 2 * Real.logb p L.sc.a * Real.log p =
        12 * (D.R.f * (Nm D ^ 2 * Real.log L.sc.a)) := by
      unfold Real.logb
      field_simp
    rw [e]
    have a : Nm D ^ 2 * Real.log L.sc.a ≤ L.etaSz * (2 * L.sc.L) := mul_le_mul hN2 la1 la0 hη.le
    have a2 := mul_le_mul_of_nonneg_left a (by positivity : (0 : ℝ) ≤ D.R.f)
    linarith

theorem sum_cube_le {D : D7} {L : SizeData₂ D} (h : SizesAt L) (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) :
    (D.R.k : ℝ) * ∑ p ∈ S, (if IsCs D p then Real.log p / (p : ℝ) ^ 3 else 0) ≤ 2 := by
  rw [← Finset.sum_filter]
  have he : 1 ≤ D.R.e := le_trans one_le_two D.host.two_le_e
  have hM := UpperTheory.sum_log_div_cube_le_of_two_pow_dvd D.R.e he (S.filter fun p => IsCs D p) (fun p hp => by
    obtain ⟨a, b⟩ := Finset.mem_filter.1 hp
    exact (UpperTheory.two_pow_dvd_sub_or_add_one_of_odd_addOrderOf_hP D p (hS p a) b.1 b.2.1).1)
  exact (mul_le_mul_of_nonneg_left hM (Nat.cast_nonneg _)).trans (cube_sizes h)

theorem sum_eatI {D : D7} {L : SizeData₂ D} (h : SizesAt L) {K : Consts} {c : ErrC} (h1 : K.dl1 = 5) (h2 : K.dl2 = 4)
    (h3 : c.c6 = 12) {j : ℕ} (hj : j ∈ SizeData₂.lifts D) (S : Finset ℕ)
    (hS : ∀ p ∈ S, p.Prime ∧ (p : ℝ) ≤ L.sc.X'' D.R.n) :
    ∑ p ∈ S, |EatI L K c j p| * Real.log p ≤ 424 * L.B0 := by
  obtain ⟨-, -, -, hX, -, -, hLη, -, h2x, -, -, hw0⟩ := nums h
  have hx1 := L.sc.one_lt_alt
  have hb : 0 < L.sc.b := Real.exp_pos _
  have hL : 1 ≤ L.sc.L := Real.one_le_rpow L.sc.one_lt_alt.le L.sc.eps_pos.le
  have hmn := D.R.two_le_m
  have hm : (1 : ℝ) ≤ D.R.m := by exact_mod_cast (by omega : 1 ≤ D.R.m)
  have hη := L.etaSz_pos
  have hX0 : 0 ≤ L.sc.X'' D.R.n := div_nonneg (mul_nonneg (by linarith) hb.le) hw0.le
  have hXb : L.sc.X'' D.R.n ≤ L.sc.b := (le_mul_of_one_le_right hX0 (by linarith)).trans hX
  have hB : L.B0 = D.R.f * D.R.m * L.sc.b * L.sc.L := rfl
  have hcard : (S.card : ℝ) ≤ L.sc.X'' D.R.n := by
    have a : S ⊆ Finset.Icc 1 ⌊L.sc.X'' D.R.n⌋₊ := fun p hp =>
      Finset.mem_Icc.2 ⟨(hS p hp).1.pos, Nat.le_floor (hS p hp).2⟩
    have a2 := Finset.card_le_card a
    rw [Nat.card_Icc, Nat.add_sub_cancel] at a2
    exact le_trans (by exact_mod_cast a2) (Nat.floor_le hX0)
  have hM := Formalism.DivisionValues.primeLogSum L.sc.b (by linarith) S (fun p hp => ⟨(hS p hp).1, (hS p hp).2.trans hXb⟩)
  have hlogb : Real.log L.sc.b = L.sc.L := Real.log_exp _
  have hl4 : Real.log 4 ≤ 2 := by
    have := Real.log_two_lt_d9
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    push_cast
    linarith
  have pt : ∀ p ∈ S, |EatI L K c j p| * Real.log p ≤
      (126 * (D.R.f * D.R.m * L.sc.b) * (Real.log p / p) +
        9 * (D.R.f * L.sc.b) * (D.R.k * if IsCs D p then Real.log p / (p : ℝ) ^ 3 else 0)) +
        70 * (D.R.f * L.etaSz * L.sc.L) := fun p hp => by
    have b1 := eatI_bound h h1 h2 h3 hj (hS p hp).1.two_le ((hS p hp).2.trans hXb)
    have b2 := eatX_bound h h3 hj (hS p hp).1.two_le
    have b3 : |EatI L K c j p| ≤ |EatI L K c j p - EatX L c j p| + |EatX L c j p| := by
      simpa using abs_add_le (EatI L K c j p - EatX L c j p) (EatX L c j p)
    have b4 := mul_le_mul_of_nonneg_right b3 (Real.log_natCast_nonneg p)
    linarith
  refine (Finset.sum_le_sum pt).trans ?_
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum,
    Finset.sum_const, nsmul_eq_mul, hB]
  have a0 := mul_le_mul_of_nonneg_left (sum_cube_le h S fun p hp => (hS p hp).1)
    (by positivity : 0 ≤ 9 * (D.R.f * L.sc.b))
  have hm2 : (2 : ℝ) ≤ D.R.m := by exact_mod_cast hmn
  have a4 := mul_le_mul_of_nonneg_left hm2 (by positivity : 0 ≤ D.R.f * L.sc.b * L.sc.L)
  have a5 := mul_le_mul_of_nonneg_left hL (by positivity : 0 ≤ D.R.f * L.sc.b)
  have a1 : 126 * (D.R.f * D.R.m * L.sc.b) * ∑ p ∈ S, Real.log p / p ≤ 126 * (D.R.f * D.R.m * L.sc.b) * (3 * L.sc.L) :=
    mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  have a2 : (S.card : ℝ) * L.etaSz ≤ L.sc.b := (mul_le_mul_of_nonneg_right hcard hη.le).trans hX
  have a3 := mul_le_mul_of_nonneg_left a2 (by positivity : 0 ≤ 70 * (D.R.f * L.sc.L))
  have a6 : 0 ≤ D.R.f * L.sc.b * L.sc.L := by positivity
  linarith

end GlobalTheory.OtherLoss

end
