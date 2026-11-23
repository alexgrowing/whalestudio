import Formalism.HermitianCurvature.StatementJ

open Finset NumberField Formalism.FourierDecayAlt Formalism.FourierDecayAlt.J

namespace Formalism.FourierDecayAlt.P.Jx11

theorem chebToThreshold : ChebToThreshold := by
  intro L f d pl sa al bt κ len lv be X B Mx hκ hlen hbt hsa h1 h2
  have hz : κ ^ (1 - (d : ℤ)) = κ * (κ ^ d)⁻¹ := by
    rw [zpow_sub₀ hκ.ne', zpow_one, zpow_natCast, div_eq_mul_inv]
  have hfac : ∀ a, (1 / 2) * (4 / (bt a - al a)) ^ d * (κ * be (pl a)) =
      κ ^ (1 - (d : ℤ)) * ((1 / 2) * be (pl a) * (4 * κ / len) ^ d) := by
    intro a
    rw [hbt a, hz, div_pow, div_pow, mul_pow]
    field_simp
  have hc0 : 0 ≤ ∏ a, (1 / 2) * (4 / (bt a - al a)) ^ d := by
    apply Finset.prod_nonneg
    intro a _
    rw [hbt a]; positivity
  have hP : 0 < ∏ _a : Fin L, κ ^ (1 - (d : ℤ)) := Finset.prod_pos (fun _ _ => zpow_pos hκ _)
  have h3 : (∏ a, sa a) * X ≤ (∏ a, (1 / 2) * (4 / (bt a - al a)) ^ d) * ((∏ a, κ * be (pl a)) * Mx) :=
    h1.trans (mul_le_mul_of_nonneg_left h2 hc0)
  have h4 : (∏ a, sa a) = (∏ _a : Fin L, κ ^ (1 - (d : ℤ))) * ∏ a, lv (pl a) := by
    rw [← Finset.prod_mul_distrib]; exact Finset.prod_congr rfl (fun a _ => hsa a)
  have h5 : (∏ a, (1 / 2) * (4 / (bt a - al a)) ^ d) * (∏ a, κ * be (pl a)) =
      (∏ _a : Fin L, κ ^ (1 - (d : ℤ))) * ∏ a, (1 / 2) * be (pl a) * (4 * κ / len) ^ d := by
    rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl (fun a _ => hfac a)
  rw [h4, ← mul_assoc, h5, mul_assoc, mul_assoc] at h3
  exact le_of_mul_le_mul_left h3 hP

theorem mix {L d : ℕ} (grid : Fin L → Fin (d + 1) → ℝ) (S : Fin L → ℝ)
    (hS : ∀ a, ∑ i, |F7.lagCo (grid a) i| = S a) (hpos : ∀ a, 0 < S a) (z : ℂ)
    (Fj : (Fin L → Fin (d + 1)) → ℂ)
    (hz : z = ∑ j : Fin L → Fin (d + 1), ((∏ a, F7.lagCo (grid a) (j a) : ℝ) : ℂ) * Fj j) (c : ℝ)
    (Mj : (Fin L → Fin (d + 1)) → ℝ) (hF : ∀ j, ‖Fj j‖ ≤ c * Mj j) :
    (∀ j, 0 ≤ F7.thGrid grid j) ∧ ∑ j, F7.thGrid grid j = 1 ∧
      ‖z‖ ≤ (∏ a, S a) * (c * ∑ j, F7.thGrid grid j * Mj j) := by
  have hth : ∀ j, F7.thGrid grid j = ∏ a, (|F7.lagCo (grid a) (j a)| / S a) := by
    intro j
    unfold F7.thGrid
    exact Finset.prod_congr rfl fun a _ => by rw [hS a]
  have hnn : ∀ j, 0 ≤ F7.thGrid grid j := by
    intro j
    rw [hth j]
    exact Finset.prod_nonneg fun a _ => div_nonneg (abs_nonneg _) (hpos a).le
  have hsum : ∑ j, F7.thGrid grid j = 1 := by
    have h1 : ∑ j : Fin L → Fin (d + 1), ∏ a, (|F7.lagCo (grid a) (j a)| / S a) =
        ∏ a, ∑ i, (|F7.lagCo (grid a) i| / S a) := by
      rw [Finset.prod_univ_sum, Fintype.piFinset_univ]
    rw [Finset.sum_congr rfl fun j _ => hth j, h1]
    apply Finset.prod_eq_one
    intro a _
    rw [← Finset.sum_div, hS a, div_self (hpos a).ne']
  have hP : 0 < ∏ a, S a := Finset.prod_pos fun a _ => hpos a
  have hco : ∀ j : Fin L → Fin (d + 1), |∏ a, F7.lagCo (grid a) (j a)| = (∏ a, S a) * F7.thGrid grid j := by
    intro j
    rw [hth j, Finset.prod_div_distrib, Finset.abs_prod, mul_div_cancel₀ _ hP.ne']
  refine ⟨hnn, hsum, ?_⟩
  rw [hz]
  calc ‖∑ j : Fin L → Fin (d + 1), ((∏ a, F7.lagCo (grid a) (j a) : ℝ) : ℂ) * Fj j‖
      ≤ ∑ j : Fin L → Fin (d + 1), ‖((∏ a, F7.lagCo (grid a) (j a) : ℝ) : ℂ) * Fj j‖ := norm_sum_le _ _
    _ ≤ ∑ j : Fin L → Fin (d + 1), (∏ a, S a) * F7.thGrid grid j * (c * Mj j) := by
        apply Finset.sum_le_sum
        intro j _
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, hco j]
        exact mul_le_mul_of_nonneg_left (hF j) (mul_nonneg hP.le (hnn j))
    _ = (∏ a, S a) * (c * ∑ j, F7.thGrid grid j * Mj j) := by
        rw [Finset.mul_sum, Finset.mul_sum]
        exact Finset.sum_congr rfl fun j _ => by ring

end Formalism.FourierDecayAlt.P.Jx11

namespace Formalism.FourierDecayAlt.P

open Jx11

theorem threshold_below_one : ThresholdBelowOne := by
  intro m C c₂ κ N I A hκ hA hc
  unfold Sz.lamThreshold
  have e : 2 * (1 - 1) + 1 - 1 = 0 := by norm_num
  rw [e, pow_zero, mul_one]
  exact mul_le_mul_of_nonneg_right hc (by positivity)

theorem letters_at_places : LettersAtPlaces := by
  intro L f K pl A φ h
  rw [← Finset.prod_fiberwise (s := univ) (g := pl) (f := fun a => φ (pl a))]
  have h1 : ∀ v : Fin f, ∏ a ∈ univ.filter (fun a => pl a = v), φ (pl a) = φ v ^ (if v ∈ A then K else 0) := by
    intro v
    rw [← h v, ← Finset.prod_const]
    apply Finset.prod_congr rfl
    intro a ha
    rw [(Finset.mem_filter.1 ha).2]
  simp only [h1]
  rw [← Finset.prod_subset (Finset.subset_univ A)]
  · apply Finset.prod_congr rfl
    intro v hv; rw [if_pos hv]
  · intro v _ hv; rw [if_neg hv, pow_zero]

theorem wave_letters : WaveLetters := by
  intro hPW hC R M _ _ _ _ _ _ Ξ n L f pl dat α β X X' κ len Mx lv be hn hκ hlen hbt hsh hs hF
  have hlt : ∀ a, α a < β a := fun a => by have := hbt a; linarith
  have h1 := hPW R M Ξ n L dat α β X X' _ hn hlt hsh hF
  exact hC L f (2 * n) pl (fun a => ‖(dat a).s‖) α β κ len lv be _ _ Mx hκ hlen hbt hs h1 le_rfl

theorem wave_letters_one : WaveLettersOne := by
  intro hPW R M _ _ _ _ _ _ Ξ L f pl dat y X X' κ Mx lv be hκ hsh hs hF
  have : Subsingleton (Fin (2 * 0 + 1)) := (inferInstance : Subsingleton (Fin 1))
  have h := hPW R M Ξ 0 L dat (fun a _ => y a) X X' hsh (fun a => Function.injective_of_subsingleton _)
  rw [Fintype.sum_subsingleton _ (fun _ => (0 : Fin (2 * 0 + 1)))] at h
  have hl : ∀ a : Fin L, F7.lagCo (fun _ : Fin (2 * 0 + 1) => y a) 0 = 1 := by
    intro a
    unfold F7.lagCo
    apply Finset.prod_eq_one
    intro i hi
    exact absurd (Subsingleton.elim _ _) (Finset.mem_erase.1 hi).1
  simp only [hl, Finset.prod_const_one, Complex.ofReal_one, one_mul] at h
  have hn : (∏ a, ‖(dat a).s‖) * ‖Ξ X X'‖ = ‖F7.Fw Ξ X X' (List.ofFn fun a => (dat a, y a)) 1 1‖ := by
    rw [← h, norm_mul, norm_prod]
  have h1 : (∏ a, ‖(dat a).s‖) = (∏ _a : Fin L, κ) * ∏ a, lv (pl a) := by
    rw [← Finset.prod_mul_distrib]; exact Finset.prod_congr rfl (fun a _ => hs a)
  have h2 : (∏ a, κ * be (pl a)) = (∏ _a : Fin L, κ) * ∏ a, be (pl a) := by
    rw [← Finset.prod_mul_distrib]
  have hP : 0 < ∏ _a : Fin L, κ := Finset.prod_pos (fun _ _ => hκ)
  rw [← hn, h1, h2, mul_assoc, mul_assoc] at hF
  exact le_of_mul_le_mul_left hF hP

theorem lift_letters : LiftLetters := by
  intro hLW hC R M _ _ _ _ _ _ Ξ n s L f pl dat A₀ A₀v e t t' α β X X' κ len Mx ov be hs hκ hlen hbt
    h0 he ht hA hA0 hB hBv ho hF
  have hlt : ∀ a, α a < β a := fun a => by have := hbt a; linarith
  have h1 := hLW R M Ξ n s L dat A₀ A₀v e t t' α β X X' _ hs h0 he ht hA hA0 hB hBv hlt hF
  exact hC L f (2 * n + s) pl (fun a => ‖1 / t a - 1 / t' a‖) α β κ len ov be _ _ Mx hκ hlen hbt ho h1 le_rfl

theorem wave_letters_mixed : WaveLettersMix := by
  intro hPW hCS R M _ _ _ _ _ _ Ξ n L f pl dat α β X X' κ len Mj lv be hn hκ hlen hbt hsh hs hF
  have hlt : ∀ a, α a < β a := fun a => by have := hbt a; linarith
  have hd : 1 ≤ 2 * n := by omega
  have hid := hPW R M Ξ n L dat (fun a => Formalism.SA.C.chebPt (α a) (β a) (2 * n)) X X' hsh
    (fun a => (hCS (α a) (β a) (2 * n) (hlt a) hd).1)
  obtain ⟨m1, m2, m3⟩ := mix (fun a => Formalism.SA.C.chebPt (α a) (β a) (2 * n))
    (fun a => (1 / 2) * (4 / (β a - α a)) ^ (2 * n))
    (fun a => (hCS (α a) (β a) (2 * n) (hlt a) hd).2)
    (fun a => by have := hlt a; have h : 0 < β a - α a := by linarith
                 positivity)
    _ _ hid _ Mj hF
  refine ⟨m1, m2, ?_⟩
  rw [norm_mul, norm_prod] at m3
  exact chebToThreshold L f (2 * n) pl (fun a => ‖(dat a).s‖) α β κ len lv be _ _ _ hκ hlen hbt hs
    m3 le_rfl

theorem lift_letters_mixed : LiftLettersMix := by
  intro hLW hCS R M _ _ _ _ _ _ Ξ n s L f pl dat A₀ A₀v e t t' α β X X' κ len Mj ov be hs hκ hlen hbt
    h0 he ht hA hA0 hB hBv ho hF
  have hlt : ∀ a, α a < β a := fun a => by have := hbt a; linarith
  have hd : 1 ≤ 2 * n + s := by omega
  have hid := hLW R M Ξ n s L dat A₀ A₀v e t t' (fun a => Formalism.SA.C.chebPt (α a) (β a) (2 * n + s)) X X'
    hs h0 he ht hA hA0 hB hBv (fun a => (hCS (α a) (β a) (2 * n + s) (hlt a) hd).1)
  obtain ⟨m1, m2, m3⟩ := mix (fun a => Formalism.SA.C.chebPt (α a) (β a) (2 * n + s))
    (fun a => (1 / 2) * (4 / (β a - α a)) ^ (2 * n + s))
    (fun a => (hCS (α a) (β a) (2 * n + s) (hlt a) hd).2)
    (fun a => by have := hlt a; have h : 0 < β a - α a := by linarith
                 positivity)
    _ _ hid _ Mj hF
  refine ⟨m1, m2, ?_⟩
  have hn : ∀ a, ‖e a * (1 / t a - 1 / t' a)‖ = ‖1 / t a - 1 / t' a‖ := by
    intro a
    rw [norm_mul]
    rcases he a with h | h <;> rw [h] <;> simp
  rw [norm_mul, norm_prod, Finset.prod_congr rfl fun a _ => hn a] at m3
  exact chebToThreshold L f (2 * n + s) pl (fun a => ‖1 / t a - 1 / t' a‖) α β κ len ov be _ _ _
    hκ hlen hbt ho m3 le_rfl

end Formalism.FourierDecayAlt.P
