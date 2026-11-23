import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeilStabilizerVolume.LocDensFFS

noncomputable section

namespace PI.VolStabW

namespace FiniteFieldCounting

theorem prod_bound {ι : Type} (δ : ι → ℝ) (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (h : ∀ j, |δ j| ≤ t) (s : Finset ι) :
    |∏ j ∈ s, (1 + δ j) - 1| ≤ t * (2 ^ s.card - 1) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert j s hj ih =>
    rw [Finset.prod_insert hj, Finset.card_insert_of_notMem hj]
    set P := ∏ j ∈ s, (1 + δ j)
    have hP : |P| ≤ 1 + |P - 1| := by
      have := abs_sub_abs_le_abs_sub P 1
      rw [abs_one] at this
      linarith
    have e : (1 + δ j) * P - 1 = (P - 1) + δ j * P := by ring
    rw [e]
    have h1 := abs_add_le (P - 1) (δ j * P)
    rw [abs_mul] at h1
    have hpow : (2 : ℝ) ^ (s.card + 1) = 2 * 2 ^ s.card := by ring
    rw [hpow]
    have h2 : |δ j| * |P| ≤ t * (1 + |P - 1|) := mul_le_mul (h j) hP (abs_nonneg _) ht0
    have h3 : 0 ≤ |P - 1| := abs_nonneg _
    nlinarith [mul_nonneg (sub_nonneg.mpr ht1) h3]

theorem ratio_bound (M a : ℕ) (ha : a ≤ M) (q : ℝ) (hq : 1 ≤ q) (δ : Fin a → ℝ)
    (h : ∀ j, |δ j| ≤ (q⁻¹) ^ 2) : |∏ j, (1 + δ j) - 1| ≤ 2 ^ M * (q⁻¹) ^ 2 := by
  have ht0 : 0 ≤ (q⁻¹) ^ 2 := by positivity
  have ht1 : (q⁻¹) ^ 2 ≤ 1 := pow_le_one₀ (inv_nonneg.mpr (by linarith)) (inv_le_one_of_one_le₀ hq)
  have := prod_bound δ _ ht0 ht1 h Finset.univ
  rw [Finset.card_univ, Fintype.card_fin] at this
  have h2 : (2 : ℝ) ^ a ≤ 2 ^ M := pow_le_pow_right₀ (by norm_num) ha
  nlinarith

theorem inv_pow_le (q : ℝ) (hq : 1 ≤ q) (m : ℕ) (hm : 2 ≤ m) : (q⁻¹) ^ m ≤ (q⁻¹) ^ 2 :=
  pow_le_pow_of_le_one (inv_nonneg.mpr (by linarith)) (inv_le_one_of_one_le₀ hq) hm

theorem exp_id (M a : ℕ) (ha : a ≤ M) : M * a + a * (M - a) = 2 * M * a - a ^ 2 := by
  have h1 : a ^ 2 ≤ 2 * M * a := by nlinarith
  zify [h1, ha]
  ring

theorem sum_exp (M : ℕ) : ∀ a, a ≤ M →
    ∑ j ∈ Finset.range a, (2 * (M - j) - 1) = 2 * M * a - a ^ 2 := by
  intro a
  induction a with
  | zero => intro _; simp
  | succ a ih =>
    intro ha
    rw [Finset.sum_range_succ, ih (by omega)]
    have h1 : a ^ 2 ≤ 2 * M * a := by nlinarith
    have h2 : (a + 1) ^ 2 ≤ 2 * M * (a + 1) := by nlinarith
    have h3 : a ≤ M := by omega
    have h4 : 1 ≤ 2 * (M - a) := by omega
    zify [h1, h2, h3, h4]
    ring

theorem split_ratio (M a : ℕ) (ha : a ≤ M) (q : ℝ) (hq : q ≠ 0) :
    (∏ i : Fin a, (q ^ M - q ^ (i : ℕ))) * q ^ (a * (M - a)) / q ^ (2 * M * a - a ^ 2) =
      ∏ i : Fin a, (1 + -(q ^ (i : ℕ) / q ^ M)) := by
  have hM : q ^ M ≠ 0 := pow_ne_zero _ hq
  have e1 : ∀ i : Fin a, q ^ M - q ^ (i : ℕ) = q ^ M * (1 + -(q ^ (i : ℕ) / q ^ M)) := by
    intro i
    field_simp
    ring
  rw [Finset.prod_congr rfl fun i _ ↦ e1 i, Finset.prod_mul_distrib, Finset.prod_const,
    Finset.card_univ, Fintype.card_fin, ← pow_mul, ← exp_id M a ha, pow_add]
  have h1 : q ^ (M * a) ≠ 0 := pow_ne_zero _ hq
  have h2 : q ^ (a * (M - a)) ≠ 0 := pow_ne_zero _ hq
  field_simp

theorem inert_ratio (M a : ℕ) (ha : a ≤ M) (q : ℝ) (hq : q ≠ 0) :
    (∏ j : Fin a, (q ^ (2 * (M - j) - 1) - (-1) ^ (M - j) * q ^ (M - j - 1))) /
        q ^ (2 * M * a - a ^ 2) =
      ∏ j : Fin a, (1 + -((-1) ^ (M - j) * q ^ (M - j - 1) / q ^ (2 * (M - j) - 1))) := by
  have e1 : ∀ j : Fin a, q ^ (2 * (M - j) - 1) - (-1) ^ (M - j) * q ^ (M - j - 1) =
      q ^ (2 * (M - j) - 1) *
        (1 + -((-1) ^ (M - j) * q ^ (M - j - 1) / q ^ (2 * (M - j) - 1))) := by
    intro j
    have : q ^ (2 * (M - j) - 1) ≠ 0 := pow_ne_zero _ hq
    field_simp
    ring
  rw [Finset.prod_congr rfl fun j _ ↦ e1 j, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum,
    Fin.sum_univ_eq_sum_range (fun j ↦ 2 * (M - j) - 1) a, sum_exp M a ha]
  have h1 : q ^ (2 * M * a - a ^ 2) ≠ 0 := pow_ne_zero _ hq
  field_simp

theorem split_delta (M a : ℕ) (ha : a + 2 ≤ M) (q : ℝ) (hq : 1 ≤ q) (i : Fin a) :
    |-(q ^ (i : ℕ) / q ^ M)| ≤ (q⁻¹) ^ 2 := by
  have hq0 : q ≠ 0 := by positivity
  have hMi : q ^ M = q ^ (i : ℕ) * q ^ (M - i) := by
    rw [← pow_add]
    congr 1
    omega
  have hi : q ^ (i : ℕ) ≠ 0 := pow_ne_zero _ hq0
  have e : q ^ (i : ℕ) / q ^ M = (q⁻¹) ^ (M - i) := by
    rw [hMi, inv_pow]
    field_simp
  rw [abs_neg, e, abs_of_nonneg (by positivity)]
  exact inv_pow_le q hq _ (by omega)

theorem inert_delta (M a : ℕ) (ha : a + 2 ≤ M) (q : ℝ) (hq : 1 ≤ q) (j : Fin a) :
    |-((-1) ^ (M - j) * q ^ (M - j - 1) / q ^ (2 * (M - j) - 1))| ≤ (q⁻¹) ^ 2 := by
  have hq0 : q ≠ 0 := by positivity
  have hexp : q ^ (2 * (M - j) - 1) = q ^ (M - j - 1) * q ^ (M - j) := by
    rw [← pow_add]
    congr 1
    omega
  have hi : q ^ (M - j - 1) ≠ 0 := pow_ne_zero _ hq0
  have e : |-((-1) ^ (M - j) * q ^ (M - j - 1) / q ^ (2 * (M - j) - 1))| = (q⁻¹) ^ (M - j) := by
    rw [abs_neg, abs_div, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul, hexp,
      abs_of_nonneg (by positivity), abs_of_nonneg (by positivity), inv_pow]
    field_simp
  rw [e]
  exact inv_pow_le q hq _ (by omega)

theorem swapR_apply (k : Type) [Field k] (y : k × k) : FiniteFieldSplitting.swapR k y = y.swap := rfl

theorem card_transport {k K : Type} [Field k] [CommRing K] [Algebra k K] (σ : K ≃ₐ[k] K)
    (e : K ≃ₐ[k] k × k) (he : ∀ x, e (σ x) = (e x).swap) {M a : ℕ}
    (J : Matrix (Fin M) (Fin M) K) (T : Matrix (Fin a) (Fin a) K) :
    Nat.card {X : Fin a → Fin M → K // ffGram (σ : K →+* K) J X = T} =
      Nat.card {Y : Fin a → Fin M → k × k //
        ffGram (FiniteFieldSplitting.swapR k) (J.map e) Y = T.map e} := by
  apply Nat.card_congr
  refine Equiv.subtypeEquiv (p := fun X ↦ ffGram (σ : K →+* K) J X = T)
    (q := fun Y ↦ ffGram (FiniteFieldSplitting.swapR k) (J.map e) Y = T.map e)
    { toFun := fun X r i ↦ e (X r i)
      invFun := fun Y r i ↦ e.symm (Y r i)
      left_inv := fun X ↦ by
        funext r i
        simp
      right_inv := fun Y ↦ by
        funext r i
        simp } ?_
  intro X
  have key : ∀ r s, ffGram (FiniteFieldSplitting.swapR k) (J.map e) (fun r i ↦ e (X r i)) r s =
      e (ffGram (σ : K →+* K) J X r s) := by
    intro r s
    simp only [ffGram, ffH, map_sum, map_mul, Matrix.map_apply, swapR_apply, ← he]
    rfl
  constructor
  · intro h
    funext r s
    change ffGram (FiniteFieldSplitting.swapR k) (J.map e) (fun r i ↦ e (X r i)) r s = _
    rw [key, h]
    rfl
  · intro h
    funext r s
    apply e.injective
    rw [← key]
    exact congrFun (congrFun h r) s

end FiniteFieldCounting

theorem fFCount_of (hS : FFSplit) (hI : FFInert) : FFCount := by
  intro M
  refine ⟨2 ^ M, ?_⟩
  intro k K _ _ _ _ σ hσ h2 J hJ hJd a ha T hT hTd
  have hq1 : (1 : ℝ) ≤ (Nat.card k : ℝ) := by exact_mod_cast Nat.card_pos (α := k)
  have hq0 : (Nat.card k : ℝ) ≠ 0 := by positivity
  rcases hσ.2 with ⟨hK, hdeg, hne⟩ | ⟨e, he⟩
  · letI : Field K := hK.toField
    rw [hI k K σ hσ.1 hdeg hne h2 M a (by omega) J hJ hJd T hT hTd,
      FiniteFieldCounting.inert_ratio M a (by omega) _ hq0]
    exact FiniteFieldCounting.ratio_bound M a (by omega) _ hq1 _
      (FiniteFieldCounting.inert_delta M a ha _ hq1)
  · have hJ' : ∀ i j, ((J.map e) j i).swap = (J.map e) i j := by
      intro i j
      simp only [Matrix.map_apply, ← he, hJ]
    have hT' : ∀ i j, ((T.map e) j i).swap = (T.map e) i j := by
      intro i j
      simp only [Matrix.map_apply, ← he, hT]
    have hJd' : IsUnit (J.map e).det := by
      have hd : e J.det = (J.map e).det := (e : K →+* k × k).map_det J
      rw [← hd]
      exact hJd.map e
    have hTd' : IsUnit (T.map e).det := by
      have hd : e T.det = (T.map e).det := (e : K →+* k × k).map_det T
      rw [← hd]
      exact hTd.map e
    rw [FiniteFieldCounting.card_transport σ e he J T, hS k M a (by omega) _ hJ' hJd' _ hT' hTd',
      FiniteFieldCounting.split_ratio M a (by omega) _ hq0]
    exact FiniteFieldCounting.ratio_bound M a (by omega) _ hq1 _
      (FiniteFieldCounting.split_delta M a ha _ hq1)

theorem fFCount_of_inert (hI : FFInert) : FFCount := fFCount_of fFSplit_holds hI

end PI.VolStabW
