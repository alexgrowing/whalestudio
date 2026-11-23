import Formalism.WachLatticeTwists.LagrangeExtensionCocycles.Statement

noncomputable section

namespace Formalism.RepresentationBoundsCohomology.N2

theorem residue_finite_holds : StatResFinite := by
  unfold StatResFinite
  intro n _ ℓ c s H hℓ hrec i m
  have hq : (0:ℝ) < ℓ - 1 := by linarith
  induction m with
  | zero => simp
  | succ m ih =>
    have h1 := hrec (i + ((m + 1 : ℕ) : ZMod n))
    have he : i + ((m + 1 : ℕ) : ZMod n) - 1 = i + (m : ZMod n) := by
      push_cast
      ring
    rw [he] at h1
    have hpow : 0 < (ℓ - 1) ^ m := pow_pos hq m
    have h2 : s (i + (m : ZMod n)) / (ℓ - 1) ^ m ≤
        (H (i + ((m + 1 : ℕ) : ZMod n)) + c + 3 + s (i + ((m + 1 : ℕ) : ZMod n)) / (ℓ - 1)) / (ℓ - 1) ^ m := by
      rw [div_eq_mul_inv, div_eq_mul_inv _ ((ℓ - 1) ^ m)]
      exact mul_le_mul_of_nonneg_right h1 (inv_nonneg.mpr hpow.le)
    have h3 : (H (i + ((m + 1 : ℕ) : ZMod n)) + c + 3 + s (i + ((m + 1 : ℕ) : ZMod n)) / (ℓ - 1)) / (ℓ - 1) ^ m =
        (H (i + ((m + 1 : ℕ) : ZMod n)) + c + 3) / (ℓ - 1) ^ m + s (i + ((m + 1 : ℕ) : ZMod n)) / (ℓ - 1) ^ (m + 1) := by
      rw [pow_succ, ← div_div]
      ring
    rw [Finset.sum_range_succ]
    linarith

theorem geom_id (K L : ℝ) (hL : 1 < L) (j : ℕ) :
    (∑ a ∈ Finset.range j, K / L ^ a) + K * L / ((L - 1) * L ^ j) = K * L / (L - 1) := by
  have hL0 : L ≠ 0 := by positivity
  have hL1 : L - 1 ≠ 0 := by
    intro h
    linarith
  induction j with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ]
    have hp : L ^ n ≠ 0 := pow_ne_zero _ hL0
    have key : K / L ^ n + K * L / ((L - 1) * L ^ (n + 1)) = K * L / ((L - 1) * L ^ n) := by
      rw [pow_succ]
      field_simp <;> ring
    linarith [ih, key]

theorem residue_at_truncation : StatResCut := by
  unfold StatResCut
  intro n _ ℓ c G Hm s H i j hℓ hc hG hHm hH hrec
  have hF : StatResFinite := residue_finite_holds
  unfold StatResFinite at hF
  have hq : (1:ℝ) < ℓ - 1 := by linarith
  have hq0 : (0:ℝ) < ℓ - 1 := by linarith
  have h1 := hF n ℓ c s H (by linarith) hrec i j
  have hK0 : (0:ℝ) ≤ 2 * G + c + 3 := by linarith
  have hsum : ∑ a ∈ Finset.range j, (H (i + ((a + 1 : ℕ) : ZMod n)) + c + 3) / (ℓ - 1) ^ a ≤
      ∑ a ∈ Finset.range j, (2 * G + c + 3) / (ℓ - 1) ^ a := by
    apply Finset.sum_le_sum
    intro a ha
    rw [Finset.mem_range] at ha
    have hb := hH (a + 1) (by omega) (by omega)
    rw [div_eq_mul_inv, div_eq_mul_inv (2 * G + c + 3)]
    apply mul_le_mul_of_nonneg_right ?_ (inv_nonneg.mpr (pow_pos hq0 a).le)
    linarith
  have hg := geom_id (2 * G + c + 3) (ℓ - 1) hq j
  have htail : 0 ≤ (2 * G + c + 3) * (ℓ - 1) / ((ℓ - 1 - 1) * (ℓ - 1) ^ j) := by
    apply div_nonneg (mul_nonneg hK0 hq0.le)
    exact mul_nonneg (by linarith) (pow_pos hq0 j).le
  have hlast : s (i + (j : ZMod n)) / (ℓ - 1) ^ j ≤ Hm / (ℓ - 1) ^ j := by
    rw [div_eq_mul_inv, div_eq_mul_inv Hm]
    exact mul_le_mul_of_nonneg_right (hHm _) (inv_nonneg.mpr (pow_pos hq0 j).le)
  have hfin : (2 * G + c + 3) * (ℓ - 1) / (ℓ - 1 - 1) = (2 * G + c + 3) * (ℓ - 1) / (ℓ - 2) := by
    rw [show ℓ - 1 - 1 = ℓ - 2 by ring]
  linarith

theorem residue_always_holds : StatResAlways := by
  unfold StatResAlways
  intro ℓ s H c r hℓ hsH hr
  have hℓR : (3:ℝ) ≤ ℓ := by exact_mod_cast hℓ
  have hq0 : (0:ℝ) < (ℓ:ℝ) - 1 := by linarith
  have hne : (ℓ:ℝ) - 1 ≠ 0 := hq0.ne'
  have hsH' : (s:ℝ) ≤ H := by exact_mod_cast hsH
  have e1 : ((ℓ - 2 : ℕ) : ℝ) = (ℓ:ℝ) - 2 := by
    rw [Nat.cast_sub (by omega : 2 ≤ ℓ)] <;> norm_num
  have e2 : ((ℓ - 1 : ℕ) : ℝ) = (ℓ:ℝ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ ℓ)] <;> norm_num
  have hd0 := Nat.cast_div_le (α := ℝ) (m := s + (ℓ - 2)) (n := ℓ - 1)
  rw [Nat.cast_add, e1, e2] at hd0
  have hA : (H:ℝ) / ((ℓ:ℝ) - 1) + 1 - ((s:ℝ) + ((ℓ:ℝ) - 2)) / ((ℓ:ℝ) - 1) =
      ((H:ℝ) - s + 1) / ((ℓ:ℝ) - 1) := by
    field_simp
    ring
  have hA0 : 0 ≤ ((H:ℝ) - s + 1) / ((ℓ:ℝ) - 1) := div_nonneg (by linarith) hq0.le
  have hB : (H:ℝ) * (2 * (ℓ:ℝ) - 1) / ((ℓ:ℝ) - 1) ^ 2 + 1 -
      (((s:ℝ) + ((ℓ:ℝ) - 2)) / ((ℓ:ℝ) - 1) + (s:ℝ) * (ℓ:ℝ) / ((ℓ:ℝ) - 1) ^ 2) =
      (((H:ℝ) - s) * (2 * (ℓ:ℝ) - 1) + ((ℓ:ℝ) - 1)) / ((ℓ:ℝ) - 1) ^ 2 := by
    field_simp
    ring
  have hB0 : 0 ≤ (((H:ℝ) - s) * (2 * (ℓ:ℝ) - 1) + ((ℓ:ℝ) - 1)) / ((ℓ:ℝ) - 1) ^ 2 := by
    apply div_nonneg ?_ (sq_nonneg _)
    have h5 : (0:ℝ) ≤ (H:ℝ) - s := by linarith
    have h6 : (0:ℝ) ≤ 2 * (ℓ:ℝ) - 1 := by linarith
    nlinarith [mul_nonneg h5 h6]
  constructor
  · linarith
  · linarith

theorem residue_quotient_holds : StatResQ := by
  unfold StatResQ
  intro A _ D _ _ N N' π₀ ℓ a r ha hr
  have hA : π₀ ^ a ∈ N'.colon N := Submodule.mem_colon.mpr ha
  have hB : (ℓ : A) ^ r ∈ N'.colon N := Submodule.mem_colon.mpr hr
  have hC := Ideal.add_pow_mem_of_pow_mem_of_le _ hA hB (show a + r ≤ a + r + 1 by omega)
  exact Submodule.mem_colon.mp hC

theorem superadditivity_holds : StatASuper := by
  unfold StatASuper
  intro ℓ _ r s
  unfold aH
  have hd : ℓ ^ (padicValNat ℓ r.factorial + padicValNat ℓ s.factorial) ∣ (r + s).factorial := by
    rw [pow_add]
    exact (Nat.mul_dvd_mul pow_padicValNat_dvd pow_padicValNat_dvd).trans
      (Nat.factorial_mul_factorial_dvd_factorial_add r s)
  have h := (padicValNat_dvd_iff_le (Nat.factorial_ne_zero _)).mp hd
  omega

theorem frame_invariance_holds : StatFrameInv := by
  unfold StatFrameInv
  intro ℓ _ E _ I Cf Cf' h0 h0' hCf hconv r
  have hsup : StatASuper := superadditivity_holds
  unfold StatASuper at hsup
  have hL : ∀ k : ℕ, ((ℓ : E) ^ k) ∈ I := fun k => pow_mem (natCast_mem I ℓ) k
  induction r using Nat.strong_induction_on with
  | _ r ih =>
    rcases Nat.eq_zero_or_pos r with hr | hr
    · subst hr
      rw [h0', mul_one]
      exact hL _
    · have hs := hconv r hr
      simp only [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, Nat.succ_eq_add_one,
        Finset.sum_range_succ', h0, one_mul, Nat.sub_zero] at hs
      have hCr : Cf' r = -∑ k ∈ Finset.range r, Cf (k + 1) * Cf' (r - (k + 1)) := by
        rw [eq_neg_iff_add_eq_zero, add_comm]
        exact hs
      rw [hCr, mul_neg, Finset.mul_sum]
      apply neg_mem
      apply sum_mem
      intro k hk
      rw [Finset.mem_range] at hk
      have hle : aH ℓ (k + 1) + aH ℓ (r - (k + 1)) ≤ aH ℓ r := by
        have h7 := hsup ℓ (k + 1) (r - (k + 1))
        rwa [Nat.add_sub_cancel' (by omega)] at h7
      have hcomm : Commute ((ℓ : E) ^ aH ℓ (r - (k + 1))) (Cf (k + 1)) :=
        (Nat.cast_commute ℓ (Cf (k + 1))).pow_left _
      have heq : (ℓ : E) ^ aH ℓ r * (Cf (k + 1) * Cf' (r - (k + 1))) =
          (ℓ : E) ^ (aH ℓ r - (aH ℓ (k + 1) + aH ℓ (r - (k + 1)))) *
            ((ℓ : E) ^ aH ℓ (k + 1) * Cf (k + 1)) *
            ((ℓ : E) ^ aH ℓ (r - (k + 1)) * Cf' (r - (k + 1))) := by
        conv_lhs => rw [← Nat.sub_add_cancel hle, pow_add, pow_add]
        simp only [mul_assoc]
        rw [← mul_assoc ((ℓ : E) ^ aH ℓ (r - (k + 1))) (Cf (k + 1)), hcomm.eq, mul_assoc]
      rw [heq]
      exact mul_mem (mul_mem (hL _) (hCf _)) (ih _ (by omega))

theorem sigma_j_numerical : StatSigJNum := by
  unfold StatSigJNum
  intro ℓ hℓ j y r hj
  have hℓR : (3:ℝ) ≤ ℓ := by exact_mod_cast hℓ
  have hq : (0:ℝ) < (ℓ:ℝ) - 1 := by linarith
  have hP : (0:ℝ) < (ℓ:ℝ) ^ (j - 1) := pow_pos (by linarith) _
  rw [← div_div]
  set Y := (y:ℝ) / (ℓ:ℝ) ^ (j - 1) with hYdef
  have e1 : (r:ℝ) * ℓ / ((ℓ:ℝ) - 1) - Y / ((ℓ:ℝ) - 1) = ((ℓ:ℝ) * r - Y) / ((ℓ:ℝ) - 1) := by
    ring
  rcases le_total ((ℓ:ℝ) * r - Y) 0 with h | h
  · rw [max_eq_left h]
    have h8 : 0 ≤ (-((ℓ:ℝ) * r - Y)) / ((ℓ:ℝ) - 1) := div_nonneg (by linarith) hq.le
    have h9 : (-((ℓ:ℝ) * r - Y)) / ((ℓ:ℝ) - 1) = -(((ℓ:ℝ) * r - Y) / ((ℓ:ℝ) - 1)) := by ring
    linarith
  · rw [max_eq_right h]
    have h8 : ((ℓ:ℝ) * r - Y) / ((ℓ:ℝ) - 1) ≤ (ℓ:ℝ) * r - Y := div_le_self h (by linarith)
    linarith

end Formalism.RepresentationBoundsCohomology.N2
