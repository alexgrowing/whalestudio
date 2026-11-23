import Mathlib
import Formalism.SharpRestriction.InertJacobiLevels.AsmIface
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.PairRowIffQdRows
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.LogAddRpowMulLogPowLeRpow

open Formalism.BasicNotions Formalism.BasicNotions.LevelStarExponents Formalism.MainNotions Formalism.MainNotions.Inhab GlobalTheory.EX NumberField

namespace GlobalTheory.EX

theorem logf_sq_le_rS : ∃ x0 : ℝ, ∀ (s : Scale) (R : Ranks), x0 ≤ s.x → RankVal s R →
    Real.log R.f ^ 2 ≤ (R.rS : ℝ) := by
  obtain ⟨x1, h1⟩ := GlobalTheory.log_add_rpow_mul_log_pow_le_rpow 0 (1 / 4) 0 36 (1 / 2) 2 le_rfl (by norm_num) (by norm_num)
  refine ⟨max x1 (Real.exp 1), fun s R hx hR => ?_⟩
  have hn := hR.n_le'
  obtain ⟨-, ⟨hm, -⟩, -, -⟩ := hR
  have hx1 := h1 s.x (le_trans (le_max_left _ _) hx)
  have hxe : Real.exp 1 ≤ s.x := le_trans (le_max_right _ _) hx
  have h1x := s.one_lt_alt
  have hx0 : 0 < s.x := by linarith
  have he := s.eps_lt
  have he0 := s.eps_pos
  have hl : 1 ≤ Real.log s.x := by
    rw [Real.le_log_iff_exp_le hx0]; exact hxe
  rw [Real.rpow_zero] at hx1
  have hm' : s.x ^ (1 / 4 : ℝ) ≤ (R.m : ℝ) := by
    refine le_trans ?_ hm
    apply Real.le_sqrt_of_sq_le
    unfold Scale.delta1
    rw [← Real.rpow_natCast, ← Real.rpow_mul hx0.le]
    have : s.x * s.x ^ (-(s.eps / 8)) = s.x ^ (1 + -(s.eps / 8)) := by
      rw [Real.rpow_add hx0, Real.rpow_one]
    rw [this]
    apply Real.rpow_le_rpow_of_exponent_le h1x.le
    push_cast
    linarith
  have hf1 : 1 ≤ R.f := by
    have : 0 < R.ord := R.ord_pos
    unfold Ranks.f Ranks.n; omega
  have hf1' : (1 : ℝ) ≤ R.f := by exact_mod_cast hf1
  have hf : (R.f : ℝ) ≤ 4 * s.x ^ (3 : ℝ) := by
    have : s.x ^ ((9 : ℝ) / 4) ≤ s.x ^ (3 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le h1x.le (by norm_num)
    unfold Ranks.f
    push_cast
    linarith
  have hlf : Real.log R.f ≤ 6 * Real.log s.x := by
    have h2 := Real.log_le_log (by linarith) hf
    rw [Real.log_mul (by norm_num) (by positivity), Real.log_rpow hx0] at h2
    have h4 : Real.log 4 ≤ 4 - 1 := Real.log_le_sub_one_of_pos (by norm_num)
    linarith
  have hlf0 : 0 ≤ Real.log R.f := Real.log_nonneg hf1'
  have hsq : Real.log R.f ^ 2 ≤ (6 * Real.log s.x) ^ 2 := pow_le_pow_left₀ hlf0 hlf 2
  have hr : R.m ≤ 2 * R.rS + 3 := by unfold Ranks.rS; omega
  have hr' : (R.m : ℝ) ≤ 2 * R.rS + 3 := by exact_mod_cast hr
  nlinarith

theorem szRow_logf : SzRow (fun C D L => (Real.log D.R.f ≤ Real.sqrt D.R.rS) ∧
    (Real.log D.R.f ^ 2 ≤ (D.R.m : ℝ) ^ 2 * L.sc.L) ∧
    (Real.log (Real.log L.sc.b) ≤ C.P.cLL * D.R.r * D.R.f * Real.log D.R.r) ∧
    ((4 * (D.R.f : ℝ) + 10) * D.R.r ≤ nW L C.P.CnW)) := by
  intro eps _ _ C hC
  obtain ⟨x1, h1⟩ := logf_sq_le_rS
  refine ⟨0, fun cD _ => ⟨0, fun ch _ => ⟨max x1 C.P.cLL⁻¹, fun D L _ hx hV => ?_⟩⟩⟩
  have hsq := h1 L.sc D.R (le_trans (le_max_left _ _) hx) hV.ranks
  have hxc : C.P.cLL⁻¹ ≤ L.sc.x := le_trans (le_max_right _ _) hx
  have hc1 : 1 ≤ C.P.cLL⁻¹ := hC.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2 _ (by simp [FC.cLast])
  have hc0 : 0 < C.P.cLL := inv_pos.mp (by linarith)
  have hW : C.P.CnW = 10 := hC.1.2.2.2.2.2.2.2.1
  obtain ⟨-, -, ⟨hk, -⟩, -⟩ := hV.ranks
  have h1x := L.sc.one_lt_alt
  have hx0 : 0 < L.sc.x := by linarith
  have he := L.sc.eps_lt
  have he0 := L.sc.eps_pos
  have hm2 := D.R.two_le_m
  have hmk := D.R.m_add_three_le_k
  have hf2 : 2 ≤ D.R.f := by
    have : 0 < D.R.ord := D.R.ord_pos
    unfold Ranks.f Ranks.n; omega
  have hf2' : (2 : ℝ) ≤ D.R.f := by exact_mod_cast hf2
  have hL : 1 ≤ L.sc.L := Real.one_le_rpow h1x.le he0.le
  have hm2' : (2 : ℝ) ≤ D.R.m := by exact_mod_cast hm2
  refine ⟨Real.le_sqrt_of_sq_le hsq, ?_, ?_, ?_⟩
  · have hr : D.R.rS ≤ D.R.m := by unfold Ranks.rS; omega
    have hr' : (D.R.rS : ℝ) ≤ D.R.m := by exact_mod_cast hr
    have h2 : (D.R.m : ℝ) ≤ (D.R.m : ℝ) ^ 2 := by nlinarith
    have h3 : (D.R.m : ℝ) ^ 2 ≤ (D.R.m : ℝ) ^ 2 * L.sc.L := le_mul_of_one_le_right (by positivity) hL
    linarith
  · have hkr : D.R.k ≤ D.R.r := by unfold Ranks.r; omega
    have hkr' : (D.R.k : ℝ) ≤ D.R.r := by exact_mod_cast hkr
    have hxk : L.sc.x ≤ L.sc.x ^ (9 / 2 + 10 * L.sc.eps) := by
      conv_lhs => rw [← Real.rpow_one L.sc.x]
      exact Real.rpow_le_rpow_of_exponent_le h1x.le (by linarith)
    have hxr : L.sc.x ≤ D.R.r := by linarith
    have hl0 : 0 ≤ Real.log L.sc.x := Real.log_nonneg h1x.le
    have hlr : Real.log L.sc.x ≤ Real.log D.R.r := Real.log_le_log hx0 hxr
    have hb : Real.log (Real.log L.sc.b) = L.sc.eps * Real.log L.sc.x := by
      unfold Scale.b Scale.L
      rw [Real.log_exp, Real.log_rpow hx0]
    have hcr : 1 ≤ C.P.cLL * D.R.r := by
      have := mul_le_mul_of_nonneg_left (le_trans hxc hxr) hc0.le
      rwa [mul_inv_cancel₀ hc0.ne'] at this
    have hcrf : 1 ≤ C.P.cLL * D.R.r * D.R.f := by nlinarith
    have h3 : Real.log D.R.r ≤ C.P.cLL * D.R.r * D.R.f * Real.log D.R.r :=
      le_mul_of_one_le_left (by linarith) hcrf
    rw [hb]
    nlinarith
  · unfold nW
    rw [hW]
    have hk1 : (1 : ℝ) ≤ D.R.k := by exact_mod_cast (by omega : 1 ≤ D.R.k)
    have hk0 : (0 : ℝ) ≤ (D.R.k : ℝ) - 1 := by linarith
    have h2 : 0 ≤ (D.R.f : ℝ) ^ 2 * ((D.R.k : ℝ) - 1) ^ 3 * L.sc.L ^ 2 / D.R.m := by positivity
    have hr0 : (0 : ℝ) ≤ D.R.r := by positivity
    nlinarith [mul_nonneg hr0 h2, mul_nonneg hr0 (sub_nonneg.mpr hf2')]

end GlobalTheory.EX
