import Mathlib
import Formalism.SharpRestriction.ElevenLe
import Formalism.SharpRestriction.Divisibility.SlopeExcess.FamilyStatementOfScaledLemmas

noncomputable section

namespace Formalism.MainNotions.DIV.HookProducts.FunSharp

open Formalism.BasicNotions Formalism.MainNotions

theorem lambda_zero_le_four_b {D : D7} (L : SizeData₂ D) (hS : SizesAt L) : lam0 D ≤ 4 * L.sc.b := by
  obtain ⟨-, -, hK, hKR, hT, -, -, -, -, -, -, -, -, hEta, hNodes, -, -, -, -, -, hG, -, -⟩ := hS
  have hx1 : 1 < L.sc.x := L.sc.one_lt_alt
  have hθ : 0 ≤ szTh L := by unfold szTh; have := L.sc.eps_pos; positivity
  have hxθ : 1 ≤ L.sc.x ^ szTh L := Real.one_le_rpow hx1.le hθ
  have hL1 : 1 ≤ L.sc.L := by unfold Scale.L; exact Real.one_le_rpow hx1.le L.sc.eps_pos.le
  have hb0 : 0 ≤ L.sc.b := by unfold Scale.b; exact (Real.exp_pos _).le
  set A : ℝ := L.sc.x ^ szTh L * L.sc.L with hA
  have hA1 : 1 ≤ A := by rw [hA]; nlinarith
  set F : ℝ := (D.R.f : ℝ) with hFdef
  set R : ℝ := (D.R.r : ℝ) with hRdef

  have hF1 : 1 ≤ F := by
    have h12 : A ≤ F * Real.log D.R.k := hKR.2.2.2.2.2.2.2.2.2.2.2.1
    by_contra hc
    have hf0 : D.R.f = 0 := by
      have : (D.R.f : ℝ) < 1 := not_le.mp hc
      exact_mod_cast Nat.lt_one_iff.mp (by exact_mod_cast this)
    rw [hFdef, hf0] at h12
    simp at h12
    linarith

  have hR1 : 1 ≤ R := by
    have hfr : F ≤ R ^ 2 := hKR.2.2.2.2.2.2.2.2.2.2.2.2.2
    have hR0 : 0 ≤ R := by positivity
    nlinarith

  have hT1 : 1 ≤ (D.R.t : ℝ) := hT.1
  have hK1 : 1 ≤ (D.R.k : ℝ) := by
    have h := hK.1
    have hp : 0 < L.sc.x ^ (9 / 2 + 10 * L.sc.eps - szTh L) := Real.rpow_pos_of_pos (by linarith) _
    have hk0 : 0 < (D.R.k : ℝ) := lt_of_lt_of_le hp h
    have : 0 < D.R.k := by exact_mod_cast hk0
    exact_mod_cast this

  have hη1 : 1 ≤ L.etaSz := hT1.trans hEta.1
  have hden : 1 ≤ (D.R.t : ℝ) ^ 3 * F * (D.R.k : ℝ) ^ 3 := by
    have h1 : 1 ≤ (D.R.t : ℝ) ^ 3 := one_le_pow₀ hT1
    have h2 : 1 ≤ (D.R.k : ℝ) ^ 3 := one_le_pow₀ hK1
    have h3 : 1 ≤ (D.R.t : ℝ) ^ 3 * F := by nlinarith
    nlinarith
  have hηb : L.etaSz ≤ L.sc.b := hEta.2.1.trans (div_le_self hb0 hden)
  have hηm : L.etaSz / D.R.m ≤ L.etaSz := by
    rcases Nat.eq_zero_or_pos D.R.m with h | h
    · rw [h, Nat.cast_zero, div_zero]; linarith
    · exact div_le_self (by linarith) (by exact_mod_cast h)
  have hQ : L.sc.x ^ szTh L * R ^ 19 * F ^ 5 * L.sc.L ≤ L.sc.b :=
    (hNodes.2.2.1.trans hηm).trans hηb

  have hF5 : F ≤ F ^ 5 := le_self_pow₀ hF1 (by norm_num)
  have hR19 : R ^ 2 ≤ R ^ 19 := pow_le_pow_right₀ hR1 (by norm_num)
  have hFR : F * R ^ 2 ≤ F ^ 5 * R ^ 19 := mul_le_mul hF5 hR19 (by positivity) (by positivity)
  have hQ' : F * R ^ 2 * A ≤ L.sc.b := by
    have : F * R ^ 2 * A ≤ F ^ 5 * R ^ 19 * A := mul_le_mul_of_nonneg_right hFR (by linarith)
    have e : F ^ 5 * R ^ 19 * A = L.sc.x ^ szTh L * R ^ 19 * F ^ 5 * L.sc.L := by rw [hA]; ring
    linarith
  have hFR0 : 0 ≤ F * R ^ 2 := by positivity
  have hFRb : F * R ^ 2 ≤ L.sc.b := le_trans (le_mul_of_one_le_right hFR0 hA1) hQ'

  have hg0 : (0 : ℝ) < D.host.g 0 := by exact_mod_cast (D.host.g_prime 0).pos
  have hg1 : (1 : ℝ) ≤ D.host.g 0 := by exact_mod_cast (D.host.g_prime 0).one_lt.le
  have hlog0 : 0 ≤ Real.log (2 * (D.host.g 0 : ℝ)) := Real.log_nonneg (by linarith)
  have hY : ∀ i, (D.host.g i : ℝ) ≤ 2 * (D.host.g 0 : ℝ) := fun i => (hG i 0).2.1
  have h0 := Formalism.MainNotions.DIV.Proofs.ScaledLatticeNorms.scaled_lattice_nonzero_holds D (D.host.g 0 : ℝ) hY
  have hlog : Real.log (2 * (D.host.g 0 : ℝ)) ≤ 1 + A := by
    rw [Real.log_mul (by norm_num) hg0.ne']
    have h2 : Real.log 2 < 1 := by have := Real.log_two_lt_d9; linarith
    have h3 : Real.log (D.host.g 0 : ℝ) ≤ A := (hG 0 0).2.2
    linarith
  calc lam0 D ≤ 2 * F * R ^ 2 * Real.log (2 * (D.host.g 0 : ℝ)) := h0
    _ ≤ 2 * F * R ^ 2 * (1 + A) := mul_le_mul_of_nonneg_left hlog (by positivity)
    _ = 2 * (F * R ^ 2) + 2 * (F * R ^ 2 * A) := by ring
    _ ≤ 4 * L.sc.b := by linarith

end Formalism.MainNotions.DIV.HookProducts.FunSharp
