import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CardFiniteSubgroupGLIntDvd
import Formalism.SharpRestriction.Divisibility.LocalQuadraticParts
import Formalism.SharpRestriction.GrowthBounds.WeilJacquetShalikaLaw
import Formalism.SharpRestriction.GlobalSchurBounds.MainIn
import Formalism.QuotientMetricDivisors.FinalW
import Formalism.QuotientMetricDivisors.SixthReductionExplicit
open Formalism.BasicNotions Formalism.BasicNotions.DV Formalism.MainNotions NumberField Classical

namespace GlobalTheory.DGamCoprime

theorem two_f_N_le (R : Ranks) (h : R.f * R.m ≤ R.k) : 2 * R.f * R.N R.m ≤ 4 * R.t * R.r := by
  have h1 : R.f ≤ R.k := R.f_le_k
  have h2 := R.two_le_m
  have h3 := R.rank_add_five_le
  have h4 : R.k ≤ R.r := by unfold Ranks.r; omega
  have h5 : R.k + 1 ≤ R.t := by omega
  unfold Ranks.N
  have e : 2 * R.f * (R.k + R.m * (R.t + 1)) = 2 * (R.f * R.k) + 2 * ((R.f * R.m) * (R.t + 1)) := by ring
  have a1 : R.f * R.k ≤ R.k * R.k := Nat.mul_le_mul_right _ h1
  have a2 : (R.f * R.m) * (R.t + 1) ≤ R.k * (R.t + 1) := Nat.mul_le_mul_right _ h
  have a3 : R.k * (R.k + 1) ≤ R.k * R.t := Nat.mul_le_mul_left _ h5
  have a4 : R.t * R.k ≤ R.t * R.r := Nat.mul_le_mul_left _ h4
  rw [e]
  nlinarith

variable {D : D7} (L : SizeData₂ D)

theorem one_le_L : 1 ≤ L.sc.L := Real.one_le_rpow L.sc.one_lt_alt.le L.sc.eps_pos.le

theorem one_le_b : 1 ≤ L.sc.b := Real.one_le_exp (by linarith [one_le_L L])

theorem f_mul_m_le (h : SizeKRel L) : D.R.f * D.R.m ≤ D.R.k := by
  have h1 := h.1
  have hx := L.sc.one_lt_alt.le
  have he := L.sc.eps_pos
  have a1 : 1 ≤ L.sc.x ^ szTh L := Real.one_le_rpow hx (by unfold szTh; positivity)
  have a2 : 1 ≤ L.sc.x ^ L.sc.eps := Real.one_le_rpow hx he.le
  have a3 := one_le_L L
  have hm : (1 : ℝ) ≤ D.R.m := by exact_mod_cast (le_trans (by norm_num) D.R.two_le_m)
  have a4 : (D.R.m : ℝ) ≤ (D.R.m : ℝ) ^ 5 := le_self_pow₀ hm (by norm_num)
  have hf : (0 : ℝ) ≤ D.R.f := Nat.cast_nonneg _
  have key : (1 : ℝ) * D.R.m * D.R.f * 1 * 1 ≤
      L.sc.x ^ szTh L * (D.R.m : ℝ) ^ 5 * D.R.f * L.sc.L * L.sc.x ^ L.sc.eps := by
    gcongr
  have : ((D.R.f * D.R.m : ℕ) : ℝ) ≤ D.R.k := by push_cast; linarith
  exact_mod_cast this

theorem q_le_sqrt_b (h : SizeCond L) (hd : 0 < D.host.d) (hq : 0 < D.host.q) :
    (D.host.q : ℝ) ≤ Real.sqrt L.sc.b := by
  unfold SizeCond at h
  have hd' : (1 : ℝ) ≤ D.host.d := by exact_mod_cast hd
  have hq' : (1 : ℝ) ≤ D.host.q := by exact_mod_cast hq
  have ht : (1 : ℝ) ≤ D.R.t := by
    have := D.R.three_m_lt_t
    exact_mod_cast (show 1 ≤ D.R.t by omega)
  have c1 : (D.host.q : ℝ) ≤ szCond L := by
    unfold szCond
    calc (D.host.q : ℝ) = 1 * D.host.q * 1 := by ring
      _ ≤ (D.host.QS : ℝ) * D.host.q * D.host.d := by gcongr; exact_mod_cast D.host.QS_pos
  have c2 : szCond L ≤ szCond L ^ 36 := le_self_pow₀ (hq'.trans c1) (by norm_num)
  have c3 : (1 : ℝ) ≤ (D.R.t : ℝ) ^ 150 := one_le_pow₀ ht
  have c4 : 0 ≤ szCond L ^ 36 := by linarith
  nlinarith

theorem primes_gt (hS : SizesAt L) (hT : L.TuGe) :
    (∀ u, 2 * D.R.f * D.R.N D.R.m + 1 < (D.mem u).A.T) ∧
    (∀ a, 2 * D.R.f * D.R.N D.R.m + 1 < D.host.g a) ∧
    2 * D.R.f * D.R.N D.R.m + 1 < D.host.q ∧ 2 * D.R.f * D.R.N D.R.m + 1 < D.host.d := by
  obtain ⟨-, -, -, hK, -, hC, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hG, -⟩ := hS
  have h0 := two_f_N_le D.R (f_mul_m_le L hK)
  obtain ⟨hq, hd⟩ := D.host.qd_big
  have hq' : 2 * D.R.f * D.R.N D.R.m + 1 < D.host.q := by omega
  have hd' : 2 * D.R.f * D.R.N D.R.m + 1 < D.host.d := by omega
  have hs := q_le_sqrt_b L hC (by omega) (by omega)
  have hb := one_le_b L
  have hsb : Real.sqrt L.sc.b ≤ L.sc.b := by
    rw [Real.sqrt_le_left (by linarith)]; nlinarith
  have hqb : (D.host.q : ℝ) ≤ L.sc.b := hs.trans hsb
  refine ⟨fun u => ?_, fun a => ?_, hq', hd'⟩
  · have hm : (2 : ℝ) ≤ D.R.m := by exact_mod_cast D.R.two_le_m
    have h1 : L.sc.b ^ (1 : ℝ) ≤ L.sc.b ^ ((D.R.m : ℝ) / 2) :=
      Real.rpow_le_rpow_of_exponent_le hb (by linarith)
    rw [Real.rpow_one] at h1
    have : (D.host.q : ℝ) ≤ ((D.mem u).A.T : ℝ) := hqb.trans (h1.trans (hT u))
    have : D.host.q ≤ (D.mem u).A.T := by exact_mod_cast this
    omega
  · have hk : (1 : ℝ) ≤ D.R.k := by
      have := D.R.m_add_three_le_k
      exact_mod_cast (show 1 ≤ D.R.k by omega)
    have h1 : L.sc.b ≤ (D.R.k : ℝ) * L.sc.b := by nlinarith
    have h2 : (D.R.k : ℝ) * L.sc.b ≤ ((D.R.k : ℝ) * L.sc.b) ^ 8 := le_self_pow₀ (hb.trans h1) (by norm_num)
    have : (D.host.q : ℝ) ≤ (D.host.g a : ℝ) := hqb.trans (h1.trans (h2.trans (hG a a).1))
    have : D.host.q ≤ D.host.g a := by exact_mod_cast this
    omega

end GlobalTheory.DGamCoprime
