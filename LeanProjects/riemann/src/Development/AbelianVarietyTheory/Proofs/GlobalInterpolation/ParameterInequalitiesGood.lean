import Mathlib
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.LFunctionPositiveConductorFourEight
import Formalism.GL3MeanSquares.PrimeCountAsymptoticInProgressions
import Formalism.FrobeniusOrbits.HostCorollaries
import Formalism.SharpRestriction.GlobalSchurBounds.MainIn
import Formalism.SharpRestriction.GlobalSchurBounds.ZetaZeroFreeRegion
open GlobalTheory.NT Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory Formalism.BasicNotions NumberField IsDedekindDomain

namespace GlobalTheory.OrbitTerms

theorem markedBound_bounds (δ : ℝ) (r : ℕ) (h0 : 0 < δ) (h1 : δ ≤ 1 / 100) :
    (1 / 10 : ℝ) ^ (6 * r + 1) ≤ Formalism.G0.markedBound δ r (Formalism.MainNotions.G.goodU δ) ∧
      Formalism.G0.markedBound δ r (Formalism.MainNotions.G.goodU δ) ≤ 1 := by
  unfold Formalism.G0.markedBound
  set u := Formalism.MainNotions.G.goodU δ with hu
  have hlo : 1 / δ ≤ (u : ℝ) := Nat.le_ceil _
  have hhi : (u : ℝ) < 1 / δ + 1 := Nat.ceil_lt_add_one (by positivity)
  have hlo' : 1 ≤ (u : ℝ) * δ := by rwa [div_le_iff₀ h0] at hlo
  have hhi' : (u : ℝ) * δ ≤ 1 + δ := by
    have := mul_le_mul_of_nonneg_right hhi.le h0.le
    rwa [add_mul, one_div, inv_mul_cancel₀ h0.ne', one_mul] at this
  have hu1 : 1 ≤ u := by
    rcases Nat.eq_zero_or_pos u with h | h
    · rw [h] at hlo'; norm_num at hlo'
    · exact h
  have hd0 : 0 ≤ 1 - δ := by linarith
  have hd1 : 1 - δ ≤ 1 := by linarith
  have hv1 : (2 * ((u / 2 : ℕ) : ℝ) ≤ u) := by
    have : 2 * (u / 2) ≤ u := by omega
    exact_mod_cast this
  have hv2 : ((u : ℝ) ≤ 2 * ((u / 2 : ℕ) : ℝ) + 1) := by
    have : u ≤ 2 * (u / 2) + 1 := by omega
    exact_mod_cast this
  set v : ℕ := u / 2 with hv
  have hB : (12 / 25 : ℝ) ≤ (1 - δ) ^ (v + 1) := by
    have := one_add_mul_le_pow (a := -δ) (by linarith) (v + 1)
    have e : (1 + -δ) = 1 - δ := by ring
    rw [e] at this
    push_cast at this
    nlinarith
  have hA : (1 / 5 : ℝ) ≤ (1 - δ) ^ u := by
    have h2 : (1 - δ) ^ ((v + 1) * 2) ≤ (1 - δ) ^ u :=
      pow_le_pow_of_le_one hd0 hd1 (by omega)
    rw [pow_mul] at h2
    nlinarith
  have hA1 : (1 - δ) ^ u ≤ 1 := pow_le_one₀ hd0 hd1
  have hC1 : (1 - δ) ^ (u - 1) ≤ 1 := pow_le_one₀ hd0 hd1
  have hC0 : 0 ≤ (1 - δ) ^ (u - 1) := pow_nonneg hd0 _
  have hCe : (1 - δ) * (1 - δ) ^ (u - 1) = (1 - δ) ^ u := by
    rw [← pow_succ']; congr 1; omega
  have hvd : (1 - δ) / 2 ≤ (v : ℝ) * δ := by nlinarith
  have hvd1 : (v : ℝ) * δ ≤ 1 := by nlinarith
  have hvd0 : 0 ≤ (v : ℝ) * δ := by positivity
  have hD : (1 / 10 : ℝ) ≤ (v : ℝ) * δ * (1 - δ) ^ (u - 1) := by
    have := mul_le_mul_of_nonneg_right hvd hC0
    nlinarith
  have hD1 : (v : ℝ) * δ * (1 - δ) ^ (u - 1) ≤ 1 := mul_le_one₀ hvd1 hC0 hC1
  constructor
  · have e : (1 / 10 : ℝ) ^ (6 * r + 1) = (1 / 10) ^ (3 * r + 1) * (1 / 10) ^ (3 * r) := by
      rw [← pow_add]; congr 1; ring
    rw [e]
    exact mul_le_mul (pow_le_pow_left₀ (by norm_num) (by linarith) _)
      (pow_le_pow_left₀ (by norm_num) hD _) (by positivity) (by positivity)
  · exact mul_le_one₀ (pow_le_one₀ (by positivity) hA1) (by positivity)
      (pow_le_one₀ (by positivity) hD1)

theorem binUpper_le (G N : ℕ) (δ : ℝ) (h0 : 0 ≤ δ) (h1 : δ ≤ 1)
    (hN : 6 * Real.exp 1 * (G : ℝ) * δ ≤ N) :
    Formalism.G0.binUpper G δ N ≤ Real.exp (-(N : ℝ)) := by
  have hd0 : 0 ≤ 1 - δ := by linarith
  set t : ℝ := Real.exp 2 with ht
  have ht1 : 1 ≤ t := Real.one_le_exp (by norm_num)
  have hs : Formalism.G0.binUpper G δ N * t ^ N ≤ (t * δ + (1 - δ)) ^ G := by
    unfold Formalism.G0.binUpper
    rw [add_pow, Finset.sum_mul]
    calc ∑ j ∈ Finset.Icc N G, (G.choose j : ℝ) * δ ^ j * (1 - δ) ^ (G - j) * t ^ N
        ≤ ∑ j ∈ Finset.Icc N G, (t * δ) ^ j * (1 - δ) ^ (G - j) * (G.choose j : ℝ) := by
          refine Finset.sum_le_sum fun j hj => ?_
          have hj' := (Finset.mem_Icc.1 hj).1
          have : t ^ N ≤ t ^ j := pow_le_pow_right₀ ht1 hj'
          calc (G.choose j : ℝ) * δ ^ j * (1 - δ) ^ (G - j) * t ^ N
              ≤ (G.choose j : ℝ) * δ ^ j * (1 - δ) ^ (G - j) * t ^ j :=
                mul_le_mul_of_nonneg_left this (by positivity)
            _ = _ := by rw [mul_pow]; ring
      _ ≤ _ := by
          refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun j _ _ => by positivity
          intro j hj
          have := (Finset.mem_Icc.1 hj).2
          exact Finset.mem_range.2 (by omega)
  have h2 : (t * δ + (1 - δ)) ^ G ≤ Real.exp (N : ℝ) := by
    have a1 : t * δ + (1 - δ) ≤ Real.exp (t * δ) := by
      have := Real.add_one_le_exp (t * δ)
      linarith
    calc (t * δ + (1 - δ)) ^ G ≤ Real.exp (t * δ) ^ G :=
          pow_le_pow_left₀ (by positivity) a1 _
      _ = Real.exp (G * (t * δ)) := by rw [Real.exp_nat_mul]
      _ ≤ _ := by
          refine Real.exp_le_exp.2 (le_trans ?_ hN)
          have e1 : t = Real.exp 1 * Real.exp 1 := by rw [ht, ← Real.exp_add]; norm_num
          have e2 : Real.exp 1 ≤ 6 := by have := Real.exp_one_lt_d9; linarith
          have e3 : t ≤ 6 * Real.exp 1 := by
            rw [e1]; exact mul_le_mul_of_nonneg_right e2 (Real.exp_pos _).le
          have : (G : ℝ) * δ * t ≤ (G : ℝ) * δ * (6 * Real.exp 1) :=
            mul_le_mul_of_nonneg_left e3 (by positivity)
          linarith
  have h3 : t ^ N = Real.exp (2 * N) := by rw [ht, ← Real.exp_nat_mul]; congr 1; ring
  have h4 : Real.exp (-(N : ℝ)) * t ^ N = Real.exp (N : ℝ) := by
    rw [h3, ← Real.exp_add]; congr 1; ring
  have h5 : Formalism.G0.binUpper G δ N * t ^ N ≤ Real.exp (-(N : ℝ)) * t ^ N := by
    rw [h4]; exact hs.trans h2
  exact le_of_mul_le_mul_right h5 (by positivity)

theorem exists_log_le_rpow (C a : ℝ) (hC : 0 < C) (ha : 0 < a) :
    ∃ x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x → C * (Real.log x + 1) ≤ x ^ a := by
  have h1 := (isLittleO_log_rpow_atTop ha).bound (c := 1 / (2 * C)) (by positivity)
  have h2 := (tendsto_rpow_atTop ha).eventually_ge_atTop (2 * C)
  have h3 := Filter.eventually_ge_atTop (1 : ℝ)
  obtain ⟨x₀, hx⟩ := Filter.eventually_atTop.1 (h1.and (h2.and h3))
  refine ⟨x₀, fun x hxx => ?_⟩
  obtain ⟨b1, b2, b3⟩ := hx x hxx
  rw [Real.norm_of_nonneg (Real.log_nonneg b3), Real.norm_of_nonneg (by positivity)] at b1
  have : C * Real.log x ≤ x ^ a / 2 := by
    calc C * Real.log x ≤ C * (1 / (2 * C) * x ^ a) := mul_le_mul_of_nonneg_left b1 hC.le
      _ = x ^ a / 2 := by field_simp
  linarith

theorem orbit_terms_le : ∀ eps : ℝ, 0 < eps → eps < 1 / 52 → ∃ Cb x₀ : ℝ, 0 < Cb ∧ ∀ s : Scale, s.eps = eps → x₀ ≤ s.x → ∀ n L₂ : ℕ, s.x ^ (eps / 4) ≤ (n : ℝ) → (n : ℝ) ≤ 2 * s.x ^ Formalism.MainNotions.G.hG s → (L₂ : ℝ) ≤ 1242 / eps → (Formalism.MainNotions.G.orbitSmallMultiplicity (Formalism.MainNotions.G.rG s) (Formalism.MainNotions.G.hG s) s.x + 1) * ((6 * Formalism.MainNotions.G.rG s + 1) * Formalism.MainNotions.G.goodU s.delta1) ≤ n ∧ (n : ℝ) * (L₂.choose (Formalism.MainNotions.G.KG s) : ℝ) * s.delta1 ^ Formalism.MainNotions.G.KG s + n * (1 - Formalism.G0.markedBound s.delta1 (Formalism.MainNotions.G.rG s) (Formalism.MainNotions.G.goodU s.delta1)) ^ Formalism.MainNotions.G.orbitSmallMultiplicity (Formalism.MainNotions.G.rG s) (Formalism.MainNotions.G.hG s) s.x + n * Formalism.G0.binUpper (Formalism.MainNotions.G.goodG' (Formalism.MainNotions.G.rG s) s.delta1 (Formalism.MainNotions.G.hG s) s.x) s.delta1 (Formalism.MainNotions.G.orbitWindowCount (Formalism.MainNotions.G.rG s) s.delta1 (Formalism.MainNotions.G.hG s) s.x - 1) ≤ Cb * s.x ^ (-2 : ℝ) := by
  intro eps he he'
  obtain ⟨h, hh⟩ : ∃ h : ℝ, h = 2 + 8 * eps := ⟨_, rfl⟩
  obtain ⟨K, hK⟩ : ∃ K : ℕ, K = ⌈8 * (h + 2) / eps⌉₊ := ⟨_, rfl⟩
  obtain ⟨r, hr⟩ : ∃ r : ℕ, r = K + 1 := ⟨_, rfl⟩
  have hh0 : 0 < h := by rw [hh]; positivity
  obtain ⟨P, hP⟩ : ∃ P : ℝ, P = (h + 3) * 10 ^ (6 * r + 1) := ⟨_, rfl⟩
  have hP0 : 0 < P := by rw [hP]; positivity
  obtain ⟨c, hc⟩ : ∃ c : ℝ, c = ((6 * r + 1 : ℕ) : ℝ) := ⟨_, rfl⟩
  have hc0 : 0 < c := by rw [hc]; positivity
  obtain ⟨x₀, hx₀⟩ := exists_log_le_rpow ((P + 2) * c * 2 + 100) (eps / 8) (by positivity)
    (by positivity)
  refine ⟨2 * 2 ^ ⌈1242 / eps⌉₊ + 4, x₀, by positivity, fun s hs hx n L₂ hn1 hn2 hL => ?_⟩
  have ehG : Formalism.MainNotions.G.hG s = h := by rw [hh, ← hs]; rfl
  have eKG : Formalism.MainNotions.G.KG s = K := by rw [hK, ← ehG, ← hs]; rfl
  have erG : Formalism.MainNotions.G.rG s = r := by rw [hr, ← eKG]; rfl
  have eδ : s.delta1 = s.x ^ (-(eps / 8)) := by rw [← hs]; rfl
  rw [ehG] at hn2
  rw [ehG, eKG, erG]
  have hx1 := s.one_lt_alt
  have hbig := hx₀ _ hx
  generalize s.delta1 = δ at *
  generalize s.x = x at *
  have hxp : 0 < x := by linarith
  have hlog : 0 ≤ Real.log x := Real.log_nonneg hx1.le
  obtain ⟨y, hy⟩ : ∃ y : ℝ, y = x ^ (eps / 8) := ⟨_, rfl⟩
  rw [← hy] at hbig
  have hPc : 0 < (P + 2) * c * 2 := by positivity
  have hy100 : 100 ≤ y := by
    have := mul_nonneg hPc.le hlog
    linarith only [this, hbig, hlog, hPc]
  have hδy : δ = y⁻¹ := by rw [eδ, hy, Real.rpow_neg hxp.le]
  have hδ0 : 0 < δ := by rw [hδy]; positivity
  have hδ1 : δ ≤ 1 / 100 := by
    rw [hδy, ← one_div]; exact one_div_le_one_div_of_le (by norm_num) hy100
  have hMe : (h + 3) * Real.log x / (10 : ℝ) ^ (-((6 * r + 1 : ℕ) : ℤ)) = P * Real.log x := by
    rw [zpow_neg, zpow_natCast, hP, div_inv_eq_mul]; ring
  have hM1 : P * Real.log x ≤ (Formalism.MainNotions.G.orbitSmallMultiplicity r h x : ℝ) := by
    unfold Formalism.MainNotions.G.orbitSmallMultiplicity; rw [hMe]; exact Nat.le_ceil _
  have hM2 : (Formalism.MainNotions.G.orbitSmallMultiplicity r h x : ℝ) ≤ P * Real.log x + 1 := by
    unfold Formalism.MainNotions.G.orbitSmallMultiplicity; rw [hMe]; exact (Nat.ceil_lt_add_one (by positivity)).le
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg _
  have hkey : ∀ T : ℝ, T ≤ Real.exp (-((h + 2) * Real.log x)) → (n : ℝ) * T ≤ 2 * x ^ (-2 : ℝ) := by
    intro T hT
    have e : Real.exp (-((h + 2) * Real.log x)) = x ^ (-(h + 2)) := by
      rw [Real.rpow_def_of_pos hxp]; congr 1; ring
    rw [e] at hT
    calc (n : ℝ) * T ≤ n * x ^ (-(h + 2)) := mul_le_mul_of_nonneg_left hT hn0
      _ ≤ 2 * x ^ h * x ^ (-(h + 2)) := mul_le_mul_of_nonneg_right hn2 (by positivity)
      _ = 2 * x ^ (-2 : ℝ) := by
        rw [mul_assoc, ← Real.rpow_add hxp]; congr 2; ring
  constructor
  · have hu : (Formalism.MainNotions.G.goodU δ : ℝ) ≤ 2 * y := by
      unfold Formalism.MainNotions.G.goodU
      have e : 1 / δ = y := by rw [hδy, one_div, inv_inv]
      rw [e]
      have := (Nat.ceil_lt_add_one (show (0 : ℝ) ≤ y by linarith)).le
      linarith
    have hyy : y * y = x ^ (eps / 4) := by
      rw [hy, ← Real.rpow_add hxp]; congr 1; ring
    have hM3 : (Formalism.MainNotions.G.orbitSmallMultiplicity r h x : ℝ) + 1 ≤ (P + 2) * (Real.log x + 1) := by
      linarith only [hM2, hlog, hP0]
    have : ((Formalism.MainNotions.G.orbitSmallMultiplicity r h x : ℝ) + 1) * (c * (Formalism.MainNotions.G.goodU δ : ℝ)) ≤ n := by
      calc ((Formalism.MainNotions.G.orbitSmallMultiplicity r h x : ℝ) + 1) * (c * (Formalism.MainNotions.G.goodU δ : ℝ))
          ≤ ((P + 2) * (Real.log x + 1)) * (c * (2 * y)) :=
            mul_le_mul hM3 (mul_le_mul_of_nonneg_left hu hc0.le) (by positivity) (by positivity)
        _ = ((P + 2) * c * 2 * (Real.log x + 1)) * y := by ring
        _ ≤ y * y := mul_le_mul_of_nonneg_right (by linarith only [hbig, hlog]) (by linarith only [hy100])
        _ ≤ n := by rw [hyy]; exact hn1
    rw [hc] at this
    exact_mod_cast this
  · have t1 : (n : ℝ) * δ ^ K ≤ 2 * x ^ (-2 : ℝ) := by
      apply hkey
      have e : δ ^ K = Real.exp (-(eps / 8 * K * Real.log x)) := by
        rw [eδ, ← Real.rpow_mul_natCast hxp.le, Real.rpow_def_of_pos hxp]; congr 1; ring
      rw [e]
      refine Real.exp_le_exp.2 (neg_le_neg (mul_le_mul_of_nonneg_right ?_ hlog))
      have : 8 * (h + 2) / eps ≤ (K : ℝ) := by rw [hK]; exact Nat.le_ceil _
      rw [div_le_iff₀ he] at this
      linarith
    have c1 : (L₂.choose K : ℝ) ≤ 2 ^ ⌈1242 / eps⌉₊ := by
      have a1 : L₂ ≤ ⌈1242 / eps⌉₊ := by
        have := hL.trans (Nat.le_ceil _)
        exact_mod_cast this
      have a2 : L₂.choose K ≤ 2 ^ ⌈1242 / eps⌉₊ :=
        (Nat.choose_le_two_pow _ _).trans (Nat.pow_le_pow_right (by norm_num) a1)
      exact_mod_cast a2
    have t1' : (n : ℝ) * (L₂.choose K : ℝ) * δ ^ K ≤ 2 ^ ⌈1242 / eps⌉₊ * (2 * x ^ (-2 : ℝ)) := by
      calc (n : ℝ) * (L₂.choose K : ℝ) * δ ^ K = (L₂.choose K : ℝ) * (n * δ ^ K) := by ring
        _ ≤ _ := mul_le_mul c1 t1 (by positivity) (by positivity)
    have t2 : (n : ℝ) * (1 - Formalism.G0.markedBound δ r (Formalism.MainNotions.G.goodU δ)) ^ Formalism.MainNotions.G.orbitSmallMultiplicity r h x ≤
        2 * x ^ (-2 : ℝ) := by
      apply hkey
      obtain ⟨m1, m2⟩ := markedBound_bounds δ r hδ0 hδ1
      obtain ⟨q, hq⟩ : ∃ q : ℝ, q = (1 / 10 : ℝ) ^ (6 * r + 1) := ⟨_, rfl⟩
      rw [← hq] at m1
      have hq0 : 0 < q := by rw [hq]; positivity
      have hPq : P * q = h + 3 := by
        rw [hP, hq, mul_assoc, ← mul_pow]; norm_num
      have a1 : 1 - Formalism.G0.markedBound δ r (Formalism.MainNotions.G.goodU δ) ≤ Real.exp (-q) := by
        have := Real.add_one_le_exp (-q)
        linarith
      calc _ ≤ Real.exp (-q) ^ Formalism.MainNotions.G.orbitSmallMultiplicity r h x := pow_le_pow_left₀ (by linarith) a1 _
        _ = Real.exp ((Formalism.MainNotions.G.orbitSmallMultiplicity r h x : ℝ) * -q) := by rw [Real.exp_nat_mul]
        _ ≤ _ := by
          refine Real.exp_le_exp.2 ?_
          have a2 := mul_le_mul_of_nonneg_right hM1 hq0.le
          have a3 : P * Real.log x * q = (h + 3) * Real.log x := by rw [← hPq]; ring
          linarith only [a2, a3, hlog]
    have t3 : (n : ℝ) * Formalism.G0.binUpper (Formalism.MainNotions.G.goodG' r δ h x) δ
        (Formalism.MainNotions.G.orbitWindowCount r δ h x - 1) ≤ 2 * x ^ (-2 : ℝ) := by
      apply hkey
      unfold Formalism.MainNotions.G.orbitWindowCount
      rw [Nat.add_sub_cancel]
      have b0 := Nat.le_ceil (max (6 * Real.exp 1 * (Formalism.MainNotions.G.goodG' r δ h x : ℝ) * δ)
        ((h + 3) * Real.logb 2 x))
      refine (binUpper_le _ _ δ hδ0.le (by linarith) ((le_max_left _ _).trans b0)).trans ?_
      refine Real.exp_le_exp.2 (neg_le_neg (le_trans ?_ ((le_max_right _ _).trans b0)))
      have l2 : Real.log x ≤ Real.logb 2 x := by
        unfold Real.logb
        have p1 : 0 < Real.log 2 := Real.log_pos (by norm_num)
        have p2 : Real.log 2 ≤ 1 := by have := Real.log_two_lt_d9; linarith
        rw [le_div_iff₀ p1]
        exact mul_le_of_le_one_right hlog p2
      exact mul_le_mul (by linarith only) l2 hlog (by linarith only [hh0])
    linarith only [t1', t2, t3]

end GlobalTheory.OrbitTerms
