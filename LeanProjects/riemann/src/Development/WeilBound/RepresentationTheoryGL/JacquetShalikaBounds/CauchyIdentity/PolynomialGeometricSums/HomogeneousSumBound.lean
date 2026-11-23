import Development.WeilBound.RepresentationTheoryGL.JacquetShalikaBounds.CauchyIdentity.SchurJT

noncomputable section

open Finset

namespace PositivityTheory.RgJS

namespace HomogeneousSumBound

theorem pow_le (A : ℝ) (hA : 0 < A) (p l k : ℕ) (h1 : p ≤ l + k) (h2 : l ≤ p + k) :
    A ^ p ≤ A ^ l * max A A⁻¹ ^ k := by
  set M := max A A⁻¹ with hM
  have hM1 : 1 ≤ M := by
    rcases le_total 1 A with h | h
    · exact h.trans (le_max_left _ _)
    · exact ((one_le_inv₀ hA).2 h).trans (le_max_right _ _)
  have hAM : A ≤ M := le_max_left _ _
  have hAiM : A⁻¹ ≤ M := le_max_right _ _
  have hl : 0 ≤ A ^ l := by positivity
  rcases le_total l p with h | h
  · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
    rw [pow_add]
    refine mul_le_mul_of_nonneg_left ?_ hl
    calc A ^ d ≤ M ^ d := pow_le_pow_left₀ hA.le hAM d
      _ ≤ M ^ k := pow_le_pow_right₀ hM1 (by omega)
  · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
    have e : A ^ p = A ^ (p + d) * A⁻¹ ^ d := by
      rw [pow_add, inv_pow, mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ hA.ne'), mul_one]
    rw [e]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    calc A⁻¹ ^ d ≤ M ^ d := pow_le_pow_left₀ (by positivity) hAiM d
      _ ≤ M ^ k := pow_le_pow_right₀ hM1 (by omega)

theorem entry_le (hG : HGen) {m m' : ℕ} (α : Fin m → ℂ) (A : ℝ) (hA : 0 < A) (hα : ∀ i, ‖α i‖ ≤ A)
    (l : Fin m' → ℕ) (i j : Fin m') :
    ‖hZ ((l j : ℤ) - j + i) α‖ ≤ ((l j + m' + 1 : ℕ) : ℝ) ^ m * A ^ l j * max A A⁻¹ ^ m' := by
  have hb := (hG m α 0 A hA.le hα (by simp)).2
  have hM : 0 ≤ max A A⁻¹ := le_trans hA.le (le_max_left _ _)
  unfold hZ
  split_ifs with hz
  · rw [norm_zero]; positivity
  · push Not at hz
    set p := ((l j : ℤ) - j + i).toNat with hp
    have hpz : (p : ℤ) = (l j : ℤ) - j + i := Int.toNat_of_nonneg hz
    have hi := i.2
    have hj := j.2
    have e1 : p ≤ l j + m' := by omega
    have e2 : l j ≤ p + m' := by omega
    refine (hb p).trans ?_
    rw [mul_assoc]
    refine mul_le_mul ?_ (pow_le A hA p (l j) m' e1 e2) (by positivity) (by positivity)
    exact pow_le_pow_left₀ (by positivity) (by exact_mod_cast (by omega : p + 1 ≤ l j + m' + 1)) m

theorem jt_le (hG : HGen) {m m' : ℕ} (α : Fin m → ℂ) (A : ℝ) (hA : 0 < A) (hα : ∀ i, ‖α i‖ ≤ A)
    (l : Fin m' → ℕ) : ‖jt α l‖ ≤ cjt m A l := by
  unfold jt cjt
  rw [Matrix.det_apply]
  refine (norm_sum_le _ _).trans ?_
  have h1 : ∀ σ : Equiv.Perm (Fin m'), ‖(Equiv.Perm.sign σ) • ∏ i, (Matrix.of fun i j : Fin m' =>
      hZ ((l j : ℤ) - j + i) α) (σ i) i‖ ≤
      ∏ j, (((l j + m' + 1 : ℕ) : ℝ) ^ m * A ^ l j * max A A⁻¹ ^ m') := by
    intro σ
    rw [Units.smul_def, zsmul_eq_mul, norm_mul, norm_prod]
    have hs : ‖((Equiv.Perm.sign σ : ℤ) : ℂ)‖ = 1 := by
      rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> simp [h]
    rw [hs, one_mul]
    exact Finset.prod_le_prod (fun _ _ => norm_nonneg _) fun i _ => by
      simpa [Matrix.of_apply] using entry_le hG α A hA hα l (σ i) i
  refine (Finset.sum_le_sum fun σ _ => h1 σ).trans (le_of_eq ?_)
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin, nsmul_eq_mul]

theorem summable_pi (g : ℕ → ℝ) (hg0 : ∀ k, 0 ≤ g k) (hg : Summable g) :
    ∀ k : ℕ, Summable fun l : Fin k → ℕ => ∏ j, g (l j)
  | 0 => Summable.of_finite
  | k + 1 => by
      have ih := summable_pi g hg0 hg k
      have hprod : Summable fun p : ℕ × (Fin k → ℕ) => g p.1 * ∏ j, g (p.2 j) := by
        refine summable_mul_of_summable_norm (f := g) (g := fun l : Fin k → ℕ => ∏ j, g (l j)) ?_ ?_
        · exact hg.congr fun k => (Real.norm_of_nonneg (hg0 k)).symm
        · exact ih.congr fun l => (Real.norm_of_nonneg (Finset.prod_nonneg fun j _ => hg0 _)).symm
      refine (Fin.consEquiv (fun _ : Fin (k + 1) => ℕ)).summable_iff.1 (hprod.congr fun p => ?_)
      simp [Fin.consEquiv, Fin.prod_univ_succ]

theorem summable_poly_geom (c N : ℕ) (r : ℝ) (hr0 : 0 ≤ r) (hr : r < 1) :
    Summable fun k : ℕ => ((k + c + 1 : ℕ) : ℝ) ^ N * r ^ k := by
  have h1 : Summable fun k : ℕ => ((k : ℝ) ^ N * r ^ k) :=
    summable_pow_mul_geometric_of_norm_lt_one N (by rw [Real.norm_of_nonneg hr0]; exact hr)
  have h2 : Summable fun k : ℕ => r ^ k := summable_geometric_of_lt_one hr0 hr
  refine Summable.of_nonneg_of_le (fun k => by positivity) (fun k => ?_)
    ((h1.add h2).mul_left ((2 * ((c : ℝ) + 1)) ^ N))
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have e1 : ((k + c + 1 : ℕ) : ℝ) ≤ 2 * ((c : ℝ) + 1) * max (k : ℝ) 1 := by
    push_cast
    rcases le_total (k : ℝ) 1 with h | h
    · rw [max_eq_right h]; nlinarith
    · rw [max_eq_left h]; nlinarith
  have e2 : max (k : ℝ) 1 ^ N ≤ (k : ℝ) ^ N + 1 := by
    rcases le_total (k : ℝ) 1 with h | h
    · rw [max_eq_right h, one_pow]; linarith [pow_nonneg hk N]
    · rw [max_eq_left h]; linarith
  calc ((k + c + 1 : ℕ) : ℝ) ^ N * r ^ k ≤ (2 * ((c : ℝ) + 1) * max (k : ℝ) 1) ^ N * r ^ k :=
        mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) e1 N) (by positivity)
    _ = (2 * ((c : ℝ) + 1)) ^ N * (max (k : ℝ) 1 ^ N * r ^ k) := by rw [mul_pow]; ring
    _ ≤ (2 * ((c : ℝ) + 1)) ^ N * ((k : ℝ) ^ N * r ^ k + r ^ k) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        nlinarith [pow_nonneg hr0 k]

end HomogeneousSumBound

open HomogeneousSumBound in
theorem homogeneous_sum_bound : HGen → SumBd := by
  intro hG m m' A B ρ hA hB hρ hρAB
  refine ⟨?_, fun α hα l => jt_le hG α A hA hα l⟩
  have hr0 : 0 ≤ ρ * A * B := by positivity
  have hMA0 : 0 ≤ max A A⁻¹ := le_trans hA.le (le_max_left _ _)
  have hMB0 : 0 ≤ max B B⁻¹ := le_trans hB.le (le_max_left _ _)
  have hg0 : ∀ k : ℕ, 0 ≤ ((k + m' + 1 : ℕ) : ℝ) ^ (m + m') * (ρ * A * B) ^ k *
      (max A A⁻¹ ^ m' * max B B⁻¹ ^ m') := fun k => by positivity
  have hgs : Summable fun k : ℕ => ((k + m' + 1 : ℕ) : ℝ) ^ (m + m') * (ρ * A * B) ^ k *
      (max A A⁻¹ ^ m' * max B B⁻¹ ^ m') := (summable_poly_geom m' (m + m') _ hr0 hρAB).mul_right _
  have hall := (summable_pi _ hg0 hgs m').mul_left (((m'.factorial : ℝ)) * (m'.factorial : ℝ))
  refine (hall.comp_injective Subtype.val_injective).congr fun l => ?_
  have key : ∀ j, ((l.1 j + m' + 1 : ℕ) : ℝ) ^ (m + m') * (ρ * A * B) ^ l.1 j *
      (max A A⁻¹ ^ m' * max B B⁻¹ ^ m') =
      (((l.1 j + m' + 1 : ℕ) : ℝ) ^ m * A ^ l.1 j * max A A⁻¹ ^ m') *
        (((l.1 j + m' + 1 : ℕ) : ℝ) ^ m' * B ^ l.1 j * max B B⁻¹ ^ m') * ρ ^ l.1 j := fun j => by
    rw [pow_add, mul_pow, mul_pow]; ring
  simp only [Function.comp_apply, cjt]
  rw [Finset.prod_congr rfl fun j _ => key j, Finset.prod_mul_distrib, Finset.prod_mul_distrib,
    Finset.prod_pow_eq_pow_sum]
  ring

end PositivityTheory.RgJS
