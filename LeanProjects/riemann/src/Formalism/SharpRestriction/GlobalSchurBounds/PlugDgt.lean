import Formalism.SharpRestriction.SmoothDesignExistence.FamilyLevelPrimeInputsOfSizes
import Formalism.SharpRestriction.SmoothDesignExistence.DesignExistsDes

noncomputable section

namespace Formalism.MainNotions

open Formalism.BasicNotions Formalism.MainNotions.Pk

theorem eventually_level_prime_coprime_stabiliser_of_design {𝒞 : FamClass} {C0 eps : ℝ} {Fm : FamP eps} (hc : Des 𝒞 C0 Fm) :
    ∃ x0 : ℝ, ∀ x, x0 ≤ x → ∀ (_ : Fm.x1 < x) (i : Fm.Ix x), WeightDegreeSizes.LevelPrimeCoprimeStabiliser (Fm.D x i) := by
  unfold Des at hc
  obtain ⟨⟨⟨_, hsm⟩, _⟩, _, hTu, _⟩ := hc
  obtain ⟨xs, hs⟩ := hsm
  obtain ⟨xt, ht⟩ := hTu
  refine ⟨max xs xt, fun x hx hx1 i => ?_⟩
  unfold WeightDegreeSizes.LevelPrimeCoprimeStabiliser
  intro u hdvd

  have hTp := ((Fm.D x i).mem u).A.T_prime
  have hle := hs x (le_of_max_le_left hx) i u _ hTp hdvd

  have hge := (ht x (le_of_max_le_right hx) i).1 u

  have hsz : SizesAt (Fm.L x i) := Fm.sizes x hx1 i
  unfold SizesAt at hsz
  obtain ⟨_, _, _, _, _, hC, _⟩ := hsz
  unfold SizeCond szCond at hC

  have h3m := (Fm.D x i).R.three_m_lt_t
  have hkt := (Fm.D x i).R.rank_add_five_le
  have hm2 := (Fm.D x i).R.two_le_m
  have hf : (Fm.D x i).R.f ≤ (Fm.D x i).R.k := (Fm.D x i).R.f_le_k
  have hN : (Fm.D x i).R.N (Fm.D x i).R.m =
      (Fm.D x i).R.k + (Fm.D x i).R.m * ((Fm.D x i).R.t + 1) := rfl
  have hf' : (Fm.D x i).R.f ≤ (Fm.D x i).R.t := by omega
  have hm' : (Fm.D x i).R.m ≤ (Fm.D x i).R.t := by omega
  have hk' : (Fm.D x i).R.k ≤ (Fm.D x i).R.t := by omega
  have ht7 : 7 ≤ (Fm.D x i).R.t := by omega

  have key : 2 * (Fm.D x i).R.f * (Fm.D x i).R.N (Fm.D x i).R.m + 1 < (Fm.D x i).R.t ^ 5 := by
    rw [hN]
    have e1 : (Fm.D x i).R.k + (Fm.D x i).R.m * ((Fm.D x i).R.t + 1) ≤
        (Fm.D x i).R.t + (Fm.D x i).R.t * ((Fm.D x i).R.t + 1) :=
      Nat.add_le_add hk' (Nat.mul_le_mul_right _ hm')
    have e2 : 2 * (Fm.D x i).R.f * ((Fm.D x i).R.k + (Fm.D x i).R.m * ((Fm.D x i).R.t + 1)) ≤
        2 * (Fm.D x i).R.t * ((Fm.D x i).R.t + (Fm.D x i).R.t * ((Fm.D x i).R.t + 1)) :=
      Nat.mul_le_mul (Nat.mul_le_mul_left 2 hf') e1
    have e3 : 2 * (Fm.D x i).R.t * ((Fm.D x i).R.t + (Fm.D x i).R.t * ((Fm.D x i).R.t + 1)) + 1 <
        (Fm.D x i).R.t ^ 5 := by
      generalize (Fm.D x i).R.t = s at ht7 ⊢
      have h49 : 49 ≤ s ^ 2 := by nlinarith
      have h5 : 49 * s ^ 3 ≤ s ^ 5 := by
        calc 49 * s ^ 3 ≤ s ^ 2 * s ^ 3 := Nat.mul_le_mul_right _ h49
          _ = s ^ 5 := by ring
      have h23 : s ^ 2 ≤ s ^ 3 := Nat.pow_le_pow_right (by omega) (by omega)
      have h13 : 1 ≤ s ^ 3 := Nat.one_le_pow _ _ (by omega)
      nlinarith
    exact lt_of_le_of_lt (Nat.add_le_add_right e2 1) e3

  have hQS : (Fm.D x i).host.QS ≠ 0 := by
    intro h0
    have hcop := (Fm.D x i).host.level_coprimeS _ ((Fm.D x i).T_level u)
    rw [h0, Nat.coprime_zero_right] at hcop
    exact hTp.one_lt.ne' hcop
  have hqd := (Fm.D x i).host.qd_big
  have hq1 : (1 : ℝ) ≤ (Fm.D x i).host.q := by exact_mod_cast (show 1 ≤ (Fm.D x i).host.q by omega)
  have hd1 : (1 : ℝ) ≤ (Fm.D x i).host.d := by exact_mod_cast (show 1 ≤ (Fm.D x i).host.d by omega)
  have hQ1 : (1 : ℝ) ≤ (Fm.D x i).host.QS := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hQS
  have hsc : (1 : ℝ) ≤ ((Fm.D x i).host.QS : ℝ) * (Fm.D x i).host.q * (Fm.D x i).host.d :=
    one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le hQ1 hq1) hd1
  have hsc36 : (1 : ℝ) ≤ (((Fm.D x i).host.QS : ℝ) * (Fm.D x i).host.q * (Fm.D x i).host.d) ^ 36 :=
    one_le_pow₀ hsc
  have htR : (7 : ℝ) ≤ (Fm.D x i).R.t := by exact_mod_cast ht7
  have ht150 : ((Fm.D x i).R.t : ℝ) ^ 150 ≤ Real.sqrt (Fm.L x i).sc.b :=
    le_trans (le_mul_of_one_le_left (by positivity) hsc36) hC
  have hbpos : 0 < (Fm.L x i).sc.b := Real.sqrt_pos.mp (lt_of_lt_of_le (by positivity) ht150)
  have ht300 : ((Fm.D x i).R.t : ℝ) ^ 300 ≤ (Fm.L x i).sc.b := by
    have hmul := mul_le_mul ht150 ht150 (by positivity) (Real.sqrt_nonneg _)
    rw [Real.mul_self_sqrt hbpos.le] at hmul
    calc ((Fm.D x i).R.t : ℝ) ^ 300 = ((Fm.D x i).R.t : ℝ) ^ 150 * ((Fm.D x i).R.t : ℝ) ^ 150 := by ring
      _ ≤ (Fm.L x i).sc.b := hmul
  have ht5 : ((Fm.D x i).R.t : ℝ) ^ 5 ≤ ((Fm.D x i).R.t : ℝ) ^ 300 :=
    pow_le_pow_right₀ (by linarith) (by norm_num)
  have hb1 : (1 : ℝ) ≤ (Fm.L x i).sc.b := by
    have : (1 : ℝ) ≤ ((Fm.D x i).R.t : ℝ) ^ 5 := one_le_pow₀ (by linarith)
    linarith
  have hm2R : (2 : ℝ) ≤ (Fm.D x i).R.m := by exact_mod_cast hm2
  have hbm : (Fm.L x i).sc.b ≤ (Fm.L x i).sc.b ^ (((Fm.D x i).R.m : ℝ) / 2) := by
    calc (Fm.L x i).sc.b = (Fm.L x i).sc.b ^ (1 : ℝ) := (Real.rpow_one _).symm
      _ ≤ (Fm.L x i).sc.b ^ (((Fm.D x i).R.m : ℝ) / 2) :=
        Real.rpow_le_rpow_of_exponent_le hb1 (by linarith)
  have hleR : (((Fm.D x i).mem u).A.T : ℝ) ≤
      ((2 * (Fm.D x i).R.f * (Fm.D x i).R.N (Fm.D x i).R.m + 1 : ℕ) : ℝ) := Nat.cast_le.mpr hle
  have hkeyR : ((2 * (Fm.D x i).R.f * (Fm.D x i).R.N (Fm.D x i).R.m + 1 : ℕ) : ℝ) <
      ((Fm.D x i).R.t : ℝ) ^ 5 := by
    have := Nat.cast_lt (α := ℝ) |>.mpr key
    rw [Nat.cast_pow] at this
    exact this
  linarith

theorem closed_eventually_levelPrimeCoprimeStabiliser (𝒞 : FamClass) (C0 : ℝ) :
    Closed (Des 𝒞 C0) fun Fm _ => ∃ x0 : ℝ, ∀ x, x0 ≤ x → ∀ (_ : Fm.x1 < x) (i : Fm.Ix x), WeightDegreeSizes.LevelPrimeCoprimeStabiliser (Fm.D x i) := by
  refine ⟨1, one_pos, fun eps _ _ => ⟨⟨0, fun _ => 0, fun _ => 0, fun _ => 0⟩, ?_⟩⟩
  intro Fm CH hc _
  exact eventually_level_prime_coprime_stabiliser_of_design hc

end Formalism.MainNotions

end
