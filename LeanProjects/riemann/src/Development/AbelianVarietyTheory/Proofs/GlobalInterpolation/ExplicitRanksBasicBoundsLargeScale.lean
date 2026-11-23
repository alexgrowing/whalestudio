import Mathlib
import Formalism.SharpRestriction.InertJacobiLevels.AsmIface
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.PairRowIffQdRows

open Formalism.BasicNotions Formalism.BasicNotions.LevelStarExponents Formalism.MainNotions Formalism.MainNotions.Inhab GlobalTheory.EX NumberField

namespace GlobalTheory.EX

theorem rank_const_absorb {x : ℝ} (hx : 1 < x) (hK : (1000 : ℝ) ≤ x ^ ((1 : ℝ) / 1000)) {a b C : ℝ}
    (hC : C ≤ 1000) (hab : a + 1 / 1000 ≤ b) : C * x ^ a ≤ x ^ b := by
  have hx0 : 0 < x := by linarith
  calc C * x ^ a ≤ x ^ ((1 : ℝ) / 1000) * x ^ a :=
        mul_le_mul_of_nonneg_right (hC.trans hK) (Real.rpow_nonneg hx0.le _)
    _ = x ^ (a + 1 / 1000) := by rw [Real.rpow_add hx0, mul_comm]
    _ ≤ x ^ b := Real.rpow_le_rpow_of_exponent_le hx.le hab

theorem rank_mul_le {x : ℝ} (hx : 0 < x) {u v a b : ℝ} (hv : 0 ≤ v) (hu : u ≤ x ^ a) (hv' : v ≤ x ^ b) :
    u * v ≤ x ^ (a + b) := by
  rw [Real.rpow_add hx]
  exact mul_le_mul hu hv' hv (Real.rpow_nonneg hx.le _)

theorem rank_basic_bounds : ∀ eps : ℝ, 0 < eps → eps < 1 / 52 → ∃ x0 : ℝ, ∀ (s : Scale) (R : Ranks), s.eps = eps → x0 ≤ s.x → RankVal s R → (R.f : ℝ) ≤ s.x ^ (3 : ℝ) ∧ (R.m : ℝ) ≤ s.x ∧ (R.r : ℝ) ≤ s.x ^ (5 : ℝ) ∧ R.k ≤ R.r ∧ R.r ≤ 2 * R.k ∧ s.L ≤ s.x ∧ 1 ≤ s.L ∧ s.x ^ ((13 : ℝ) / 2) ≤ (R.f : ℝ) * R.r * s.L ∧ (R.f : ℝ) * R.r * s.L ≤ s.x ^ ((687 : ℝ) / 100) ∧ ((R.f * R.r.choose 2 : ℕ) : ℝ) ≤ s.x ^ (12 : ℝ) ∧ (R.k : ℝ) * R.f / R.m ≤ s.x ^ (7 : ℝ) ∧ ((nWv R s : ℕ) : ℝ) ≤ s.x ^ ((229 : ℝ) / 10) ∧ s.x ^ (377 : ℝ) ≤ (R.t : ℝ) ∧ (R.t : ℝ) ≤ s.x ^ (401 : ℝ) ∧ (R.N R.m : ℝ) ≤ s.x ^ (402 : ℝ) ∧ s.x ^ ((1 : ℝ) / 2 - s.eps / 16) ≤ (R.m : ℝ) ∧ (R.m : ℝ) ≤ 2 * s.x ^ ((1 : ℝ) / 2 - s.eps / 16) := by
  intro eps he0 he1
  refine ⟨(1000 : ℝ) ^ (1000 : ℝ), fun s R hs hx0 hR => ?_⟩
  have hn2 := RankVal.n_le hR
  obtain ⟨⟨hn1, -⟩, ⟨hm1, hm2⟩, ⟨hk1, hk2⟩, ht⟩ := hR
  have hx := s.one_lt_alt
  have hxp : 0 < s.x := lt_trans one_pos hx
  have e0 := s.eps_pos
  have e1 := s.eps_lt
  have hK : (1000 : ℝ) ≤ s.x ^ ((1 : ℝ) / 1000) := by
    calc (1000 : ℝ) = ((1000 : ℝ) ^ (1000 : ℝ)) ^ ((1 : ℝ) / 1000) := by
          rw [← Real.rpow_mul (by norm_num)]; norm_num
      _ ≤ _ := Real.rpow_le_rpow (by positivity) hx0 (by norm_num)
  clear hx0
  have ab : ∀ {a b C : ℝ}, C ≤ 1000 → a + 1 / 1000 ≤ b → C * s.x ^ a ≤ s.x ^ b :=
    fun hC hab => rank_const_absorb hx hK hC hab
  have mono : ∀ {a b : ℝ}, a ≤ b → s.x ^ a ≤ s.x ^ b :=
    fun h => Real.rpow_le_rpow_of_exponent_le hx.le h
  have one : ∀ {a : ℝ}, 0 ≤ a → 1 ≤ s.x ^ a := fun h => Real.one_le_rpow hx.le h
  have hsq : Real.sqrt (s.x * s.delta1) = s.x ^ ((1 : ℝ) / 2 - s.eps / 16) := by
    have : s.x * s.delta1 = s.x ^ (1 + -(s.eps / 8)) := by
      rw [Real.rpow_add hxp, Real.rpow_one]; rfl
    rw [this, Real.sqrt_eq_rpow, ← Real.rpow_mul hxp.le]
    congr 1; ring
  rw [hsq] at hm1 hm2
  have h2m := R.two_le_m
  have hmk := R.m_add_three_le_k
  have hkr : R.k ≤ R.r := by unfold Ranks.r; omega
  have hrk : R.r ≤ 2 * R.k := by unfold Ranks.r; omega
  have hkr' : (R.k : ℝ) ≤ R.r := by exact_mod_cast hkr
  have hrk' : (R.r : ℝ) ≤ 2 * R.k := by exact_mod_cast hrk
  have hfn : (R.f : ℝ) = 2 * R.n := by unfold Ranks.f; push_cast; ring
  have hf : (R.f : ℝ) ≤ s.x ^ ((2156 : ℝ) / 1000) := by
    have := ab (C := 4) (a := 2 + 8 * s.eps + s.eps / 100) (b := 2156 / 1000) (by norm_num) (by linarith)
    linarith
  have hr : (R.r : ℝ) ≤ s.x ^ ((4694 : ℝ) / 1000) := by
    have := ab (C := 4) (a := 9 / 2 + 10 * s.eps) (b := 4694 / 1000) (by norm_num) (by linarith)
    linarith
  have hk : (R.k : ℝ) ≤ s.x ^ ((4694 : ℝ) / 1000) := hkr'.trans hr
  have hL : s.L ≤ s.x ^ ((20 : ℝ) / 1000) := mono (by linarith)
  have hL1 : 1 ≤ s.L := one e0.le
  have hmu : (R.m : ℝ) ≤ s.x ^ ((501 : ℝ) / 1000) := by
    have := ab (C := 2) (a := 1 / 2 - s.eps / 16) (b := 501 / 1000) (by norm_num) (by linarith)
    linarith
  have hmp : (0 : ℝ) < R.m := by exact_mod_cast (by omega : 0 < R.m)
  have hmi : (R.m : ℝ)⁻¹ ≤ s.x ^ (-(498 : ℝ) / 1000) := by
    have h1 : s.x ^ ((498 : ℝ) / 1000) ≤ R.m := (mono (by linarith)).trans hm1
    rw [neg_div, Real.rpow_neg hxp.le]
    exact inv_anti₀ (by positivity) h1
  have f0 : (0 : ℝ) ≤ R.f := by positivity
  have r0 : (0 : ℝ) ≤ R.r := by positivity
  have k0 : (0 : ℝ) ≤ R.k := by positivity
  have L0 : (0 : ℝ) ≤ s.L := by linarith
  have mi0 : (0 : ℝ) ≤ (R.m : ℝ)⁻¹ := by positivity
  have k1 : (1 : ℝ) ≤ R.k := by exact_mod_cast (by omega : 1 ≤ R.k)
  have hf1 : 1 ≤ R.f := by
    have : 0 < R.f := by unfold Ranks.f Ranks.n; positivity
    omega
  have hf1' : (1 : ℝ) ≤ R.f := by exact_mod_cast hf1
  have hfr := rank_mul_le hxp r0 hf hr

  have hB0 : 0 ≤ (R.f : ℝ) ^ 2 * ((R.k : ℝ) - 1) ^ 3 * s.L ^ 2 / R.m := by
    have : (0 : ℝ) ≤ (R.k : ℝ) - 1 := by linarith
    positivity
  have hApos : 0 < 10 * (R.r : ℝ) * ((R.f : ℝ) + (R.f : ℝ) ^ 2 * ((R.k : ℝ) - 1) ^ 3 * s.L ^ 2 / R.m) / 8 := by
    have : (0 : ℝ) < R.r := by linarith
    have : (0 : ℝ) < (R.f : ℝ) + (R.f : ℝ) ^ 2 * ((R.k : ℝ) - 1) ^ 3 * s.L ^ 2 / R.m := by linarith
    positivity
  have hW1 : 1 ≤ nWv R s := by
    have := Nat.ceil_pos.mpr hApos
    unfold nWv; omega
  have hW : ((nWv R s : ℕ) : ℝ) ≤ s.x ^ ((229 : ℝ) / 10) := by
    have h1 := (Nat.ceil_lt_add_one hApos.le).le
    have hk' : (R.k : ℝ) - 1 ≤ s.x ^ ((4694 : ℝ) / 1000) := by linarith
    have k0' : (0 : ℝ) ≤ (R.k : ℝ) - 1 := by linarith
    have h2 := rank_mul_le hxp mi0 (rank_mul_le hxp L0 (rank_mul_le hxp L0 (rank_mul_le hxp k0'
      (rank_mul_le hxp k0' (rank_mul_le hxp k0' (rank_mul_le hxp f0 hfr hf) hk') hk') hk') hL) hL) hmi
    have h3 := h2.trans (mono (b := 227 / 10) (by norm_num))
    have h4 := hfr.trans (mono (b := 227 / 10) (by norm_num))
    have h5 : 1 ≤ s.x ^ ((227 : ℝ) / 10) := one (by norm_num)
    have h6 := ab (C := 28) (a := 227 / 10) (b := 229 / 10) (by norm_num) (by norm_num)
    have h7 : 10 * (R.r : ℝ) * ((R.f : ℝ) + (R.f : ℝ) ^ 2 * ((R.k : ℝ) - 1) ^ 3 * s.L ^ 2 / R.m) / 8
        = (10 * ((R.f : ℝ) * R.r) + 10 * ((R.f : ℝ) * R.r * R.f * ((R.k : ℝ) - 1) * ((R.k : ℝ) - 1)
          * ((R.k : ℝ) - 1) * s.L * s.L * (R.m : ℝ)⁻¹)) / 8 := by
      rw [div_eq_mul_inv ((R.f : ℝ) ^ 2 * ((R.k : ℝ) - 1) ^ 3 * s.L ^ 2)]; ring
    unfold nWv
    push_cast
    linarith
  have hT1 : s.x ^ (377 : ℝ) ≤ (TOv s : ℝ) := Nat.le_ceil _
  have hT2 : (TOv s : ℝ) ≤ s.x ^ (378 : ℝ) := by
    have h1 : (TOv s : ℝ) ≤ s.x ^ (377 : ℝ) + 1 := (Nat.ceil_lt_add_one (by positivity)).le
    have h5 : 1 ≤ s.x ^ (377 : ℝ) := one (by norm_num)
    have h6 := ab (C := 2) (a := 377) (b := 378) (by norm_num) (by norm_num)
    linarith
  have ht1 : TOv s ≤ R.t := by
    have h1 : TOv s ≤ TOv s * nWv R s := Nat.le_mul_of_pos_right _ hW1
    have h2 : R.r ≤ 8 * R.f * R.r := Nat.le_mul_of_pos_left _ (by omega)
    omega
  have ht2 : (R.t : ℝ) ≤ s.x ^ (401 : ℝ) := by
    have h1 : R.t ≤ 8 * R.f * R.r + 4 + TOv s * nWv R s := by omega
    have h2 : (R.t : ℝ) ≤ 8 * (R.f * R.r) + 4 + TOv s * nWv R s := by
      have : ((R.t : ℕ) : ℝ) ≤ ((8 * R.f * R.r + 4 + TOv s * nWv R s : ℕ) : ℝ) := by exact_mod_cast h1
      push_cast at this; linarith
    have h3 := (rank_mul_le hxp (by positivity) hT2 hW).trans (mono (b := 4009 / 10) (by norm_num))
    have h4 := hfr.trans (mono (b := 4009 / 10) (by norm_num))
    have h5 : 1 ≤ s.x ^ ((4009 : ℝ) / 10) := one (by norm_num)
    have h6 := ab (C := 13) (a := 4009 / 10) (b := 401) (by norm_num) (by norm_num)
    linarith
  refine ⟨hf.trans (mono (by norm_num)), ?_, hr.trans (mono (by norm_num)), hkr, hrk, ?_, hL1, ?_, ?_, ?_, ?_,
    hW, hT1.trans (by exact_mod_cast ht1), ht2, ?_, hm1, hm2⟩
  · simpa using hmu.trans (mono (b := 1) (by norm_num))
  · simpa using hL.trans (mono (b := 1) (by norm_num))
  · have h1 : s.x ^ (2 : ℝ) ≤ R.f := by
      have := mono (a := 2) (b := 2 + 8 * s.eps) (by linarith)
      have : (0 : ℝ) ≤ R.n := by positivity
      linarith
    have h2 : s.x ^ ((9 : ℝ) / 2) ≤ R.r := by
      have := mono (a := 9 / 2) (b := 9 / 2 + 10 * s.eps) (by linarith)
      linarith
    calc s.x ^ ((13 : ℝ) / 2) = s.x ^ (2 : ℝ) * s.x ^ ((9 : ℝ) / 2) * 1 := by
          rw [← Real.rpow_add hxp]; norm_num
      _ ≤ _ := by gcongr
  · exact (rank_mul_le hxp L0 hfr hL).trans (mono (by norm_num))
  · have h1 : ((R.r.choose 2 : ℕ) : ℝ) ≤ R.r * R.r := by
      have := Nat.choose_le_pow R.r 2
      rw [sq] at this
      exact_mod_cast this
    have h2 := (rank_mul_le hxp r0 hfr hr).trans (mono (b := 12) (by norm_num))
    push_cast
    calc (R.f : ℝ) * (R.r.choose 2 : ℕ) ≤ R.f * (R.r * R.r) := by gcongr
      _ ≤ _ := by rw [← mul_assoc]; exact h2
  · rw [div_eq_mul_inv]
    exact (rank_mul_le hxp mi0 (rank_mul_le hxp f0 hk hf) hmi).trans (mono (by norm_num))
  · have h3 := (rank_mul_le hxp (by positivity) hmu ht2).trans (mono (b := 4016 / 10) (by norm_num))
    have h4 := hk.trans (mono (b := 4016 / 10) (by norm_num))
    have h5 := hmu.trans (mono (b := 4016 / 10) (by norm_num))
    have h6 := ab (C := 3) (a := 4016 / 10) (b := 402) (by norm_num) (by norm_num)
    unfold Ranks.N
    push_cast
    linarith

end GlobalTheory.EX
