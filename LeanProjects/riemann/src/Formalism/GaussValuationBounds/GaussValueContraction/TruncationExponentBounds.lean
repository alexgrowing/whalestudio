import Formalism.GaussValuationBounds.Statement
import Formalism.WachModuleLifts.WachModuleProofs.LemmaHLift

namespace Formalism.NOK

theorem powMemSpanPow : PowContent := by
  intro A _ a X p N M z c hN hp hz
  obtain ⟨α, β, rfl⟩ := Ideal.mem_span_pair.mp hp
  obtain ⟨q, hqd⟩ : ∃ q, q = (M + N - 1) / N := ⟨_, rfl⟩
  rw [← hqd] at hz
  have hq : M ≤ N * q := by
    have h1 := Nat.div_add_mod (M + N - 1) N
    have h2 := Nat.mod_lt (M + N - 1) (by omega : 0 < N)
    rw [← hqd] at h1
    generalize N * q = w at h1 ⊢
    omega
  rw [add_pow]
  refine Ideal.sum_mem _ fun i _ => ?_
  by_cases hci : c ≤ i
  · have hmem : (α * a) ^ i ∈ Ideal.span {a ^ c, X ^ M} := by
      rw [show (α * a) ^ i = (α ^ i * a ^ (i - c)) * a ^ c by
        rw [mul_pow, mul_assoc, ← pow_add, Nat.sub_add_cancel hci]]
      exact Ideal.mul_mem_left _ _ (Ideal.subset_span (Set.mem_insert _ _))
    exact Ideal.mul_mem_right _ _ (Ideal.mul_mem_right _ _ hmem)
  · have hle : M ≤ N * (z - i) := le_trans hq (Nat.mul_le_mul_left _ (by omega))
    have hmem : (β * X ^ N) ^ (z - i) ∈ Ideal.span {a ^ c, X ^ M} := by
      rw [show (β * X ^ N) ^ (z - i) = (β ^ (z - i) * X ^ (N * (z - i) - M)) * X ^ M by
        rw [mul_pow, ← pow_mul, mul_assoc, ← pow_add, Nat.sub_add_cancel hle]]
      exact Ideal.mul_mem_left _ _ (Ideal.subset_span (Set.mem_insert_of_mem _ (Set.mem_singleton _)))
    exact Ideal.mul_mem_right _ _ (Ideal.mul_mem_left _ _ hmem)

theorem powMemSpanOfLe : RelVanish := by
  intro A _ ℓ X u p E M j r hM hE
  rw [Ideal.mem_span_singleton, mul_pow, mul_pow, ← Finset.prod_pow, mul_assoc]
  have h1 : X ^ M ∣ X ^ r := pow_dvd_pow X hM
  have h2 : ∏ s ∈ Finset.range j, p s ^ E ∣ ∏ s ∈ Finset.range j, (p s ^ (ℓ - 1)) ^ r :=
    Finset.prod_dvd_prod_of_dvd _ _ fun s _ => by
      rw [← pow_mul]
      exact pow_dvd_pow _ hE
  exact Dvd.dvd.mul_left (mul_dvd_mul h1 h2) _

private theorem prime_sub_one_mul_padicValNat_factorial_le (ℓ : ℕ) [Fact ℓ.Prime] (r : ℕ) :
    ((ℓ : ℝ) - 1) * (padicValNat ℓ r.factorial : ℝ) ≤ r := by
  have h2 : (ℓ - 1) * padicValNat ℓ r.factorial ≤ r := by
    rw [sub_one_mul_padicValNat_factorial]
    exact Nat.sub_le _ _
  have h1 : 1 ≤ ℓ := (Fact.out : ℓ.Prime).one_lt.le
  have h3 : (((ℓ - 1) * padicValNat ℓ r.factorial : ℕ) : ℝ) ≤ r := by exact_mod_cast h2
  push_cast [Nat.cast_sub h1] at h3
  exact h3

theorem truncationExponentBounds : SigNum := by
  intro ℓ _ hℓ E M j r hj
  have hℓ' : (3 : ℝ) ≤ ℓ := by exact_mod_cast hℓ
  have hL0 : (0 : ℝ) < (ℓ : ℝ) - 1 := by linarith
  have hM0 : (0 : ℝ) ≤ (M : ℝ) / (ℓ : ℝ) ^ (j - 1) := by positivity
  have hsig : ((E : ℝ) + (M : ℝ) / (ℓ : ℝ) ^ (j - 1)) * ℓ / ((ℓ : ℝ) - 1) ^ 2 < sigNOK ℓ E M j := by
    unfold sigNOK
    push_cast
    exact Nat.lt_floor_add_one _
  have hleg := prime_sub_one_mul_padicValNat_factorial_le ℓ r
  have hsub : ((ℓ - 1 : ℕ) : ℝ) = (ℓ : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ ℓ), Nat.cast_one]
  constructor
  · intro hr
    have hr' : ((ℓ : ℝ) - 1) * r < E := by
      have h := (Nat.cast_lt (α := ℝ)).2 hr
      push_cast [hsub] at h
      exact h
    have key : ((r + padicValNat ℓ r.factorial : ℕ) : ℝ) < sigNOK ℓ E M j := by
      refine lt_of_le_of_lt ?_ hsig
      rw [le_div_iff₀ (by positivity)]
      push_cast
      nlinarith [mul_le_mul_of_nonneg_left hleg hL0.le, mul_le_mul_of_nonneg_right hr'.le (by linarith : (0 : ℝ) ≤ ℓ)]
    exact_mod_cast key
  · refine le_trans ?_ hsig.le
    rcases le_or_gt (((ℓ : ℝ) - 1) * r - E - (M : ℝ) / (ℓ : ℝ) ^ (j - 1)) 0 with h | h
    · rw [max_eq_left h, sub_zero, div_le_div_iff₀ hL0 (by positivity)]
      have h' : ((ℓ : ℝ) - 1) * r ≤ E + (M : ℝ) / (ℓ : ℝ) ^ (j - 1) := by linarith
      nlinarith [mul_le_mul_of_nonneg_right h' (by positivity : (0 : ℝ) ≤ ℓ * ((ℓ : ℝ) - 1))]
    · rw [max_eq_right h.le]
      have hneg : (ℓ : ℝ) - ((ℓ : ℝ) - 1) ^ 2 < 0 := by nlinarith
      have e : (r : ℝ) * ℓ / ((ℓ : ℝ) - 1) - (((ℓ : ℝ) - 1) * r - E - (M : ℝ) / (ℓ : ℝ) ^ (j - 1)) -
          ((E : ℝ) + (M : ℝ) / (ℓ : ℝ) ^ (j - 1)) * ℓ / ((ℓ : ℝ) - 1) ^ 2 =
          (((ℓ : ℝ) - 1) * r - (E + (M : ℝ) / (ℓ : ℝ) ^ (j - 1))) * ((ℓ : ℝ) - ((ℓ : ℝ) - 1) ^ 2) /
            ((ℓ : ℝ) - 1) ^ 2 := by
        field_simp
        ring
      have hn : (((ℓ : ℝ) - 1) * r - (E + (M : ℝ) / (ℓ : ℝ) ^ (j - 1))) * ((ℓ : ℝ) - ((ℓ : ℝ) - 1) ^ 2) /
          ((ℓ : ℝ) - 1) ^ 2 ≤ 0 :=
        div_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonneg_of_nonpos (by linarith) hneg.le) (sq_nonneg _)
      linarith

theorem scaledPowMemSpan : RelCoeff := by
  intro A _ ℓ _ hℓ X u p E M j hj hp r
  set σ := sigNOK ℓ E M j with hσ
  set v := padicValNat ℓ r.factorial with hv
  set J := Ideal.span {(ℓ : A) ^ (r + v), X ^ M * ∏ s ∈ Finset.range j, p s ^ E} with hJ
  have hmem1 : (ℓ : A) ^ (r + v) ∈ J := Ideal.subset_span (Set.mem_insert _ _)
  have hmem2 : X ^ M * ∏ s ∈ Finset.range j, p s ^ E ∈ J :=
    Ideal.subset_span (Set.mem_insert_of_mem _ (Set.mem_singleton _))
  by_cases hA : r + v ≤ σ
  · rw [← Nat.sub_add_cancel hA, pow_add]
    exact J.mul_mem_right _ (J.mul_mem_left _ hmem1)
  rw [not_le] at hA
  have hℓ' : (3 : ℝ) ≤ ℓ := by exact_mod_cast hℓ
  have hL0 : (0 : ℝ) < (ℓ : ℝ) - 1 := by linarith
  have hN0 : (0 : ℝ) < (ℓ : ℝ) ^ (j - 1) := by positivity
  have hM0 : (0 : ℝ) ≤ (M : ℝ) / (ℓ : ℝ) ^ (j - 1) := by positivity
  have hleg := prime_sub_one_mul_padicValNat_factorial_le ℓ r
  have hB := (truncationExponentBounds ℓ hℓ E M j r hj).2
  have h1 : (r : ℝ) + v ≤ r * ℓ / ((ℓ : ℝ) - 1) := by
    rw [le_div_iff₀ hL0]
    nlinarith [hleg]
  have hσr : (σ : ℝ) < r + v := by exact_mod_cast hA
  have hmx : max 0 (((ℓ : ℝ) - 1) * r - E - (M : ℝ) / (ℓ : ℝ) ^ (j - 1)) =
      ((ℓ : ℝ) - 1) * r - E - (M : ℝ) / (ℓ : ℝ) ^ (j - 1) := by
    apply max_eq_right
    by_contra hneg
    rw [not_le] at hneg
    rw [max_eq_left hneg.le] at hB
    linarith
  rw [hmx] at hB
  have hc : ((r + v - σ : ℕ) : ℝ) ≤ ((ℓ : ℝ) - 1) * r - E - (M : ℝ) / (ℓ : ℝ) ^ (j - 1) := by
    rw [Nat.cast_sub hA.le]
    push_cast
    linarith
  have hsub : ((ℓ - 1 : ℕ) : ℝ) = (ℓ : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ ℓ), Nat.cast_one]
  have hE : E ≤ (ℓ - 1) * r := by
    have h0 : (0 : ℝ) ≤ ((r + v - σ : ℕ) : ℝ) := Nat.cast_nonneg _
    have : (E : ℝ) ≤ ((ℓ - 1) * r : ℕ) := by
      push_cast [hsub]
      linarith
    exact_mod_cast this
  by_cases hMr : M ≤ r
  · have hv' := powMemSpanOfLe A ℓ X u p E M j r hMr hE
    have hle : Ideal.span {X ^ M * ∏ s ∈ Finset.range j, p s ^ E} ≤ J :=
      Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hmem2)
    exact J.mul_mem_left _ (hle hv')
  rw [not_le] at hMr
  obtain ⟨c, hcd⟩ : ∃ c, c = r + v - σ := ⟨_, rfl⟩
  obtain ⟨z, hzd⟩ : ∃ z, z = (ℓ - 1) * r - E := ⟨_, rfl⟩
  rw [← hcd] at hc
  have hzr : (z : ℝ) = ((ℓ : ℝ) - 1) * r - E := by
    rw [hzd, Nat.cast_sub hE]
    push_cast [hsub]
    ring
  have hN1 : 1 ≤ ℓ ^ (j - 1) := Nat.one_le_pow _ _ (by omega)
  have hcz : c ≤ z := by
    have : (c : ℝ) ≤ z := by rw [hzr]; linarith
    exact_mod_cast this
  have hMN : M - r ≤ (z - c) * ℓ ^ (j - 1) := by
    have hreal : ((M - r : ℕ) : ℝ) ≤ ((z - c : ℕ) : ℝ) * ((ℓ ^ (j - 1) : ℕ) : ℝ) := by
      rw [Nat.cast_sub hMr.le, Nat.cast_sub hcz]
      push_cast
      have hdiv : (M : ℝ) / (ℓ : ℝ) ^ (j - 1) ≤ z - c := by rw [hzr]; linarith
      rw [div_le_iff₀ hN0] at hdiv
      have : (0 : ℝ) ≤ r := Nat.cast_nonneg _
      linarith
    exact_mod_cast hreal
  have hz : c + (M - r + ℓ ^ (j - 1) - 1) / ℓ ^ (j - 1) ≤ z + 1 := by
    have hlt : (M - r + ℓ ^ (j - 1) - 1) / ℓ ^ (j - 1) < z - c + 1 := by
      rw [Nat.div_lt_iff_lt_mul (by omega), add_mul, one_mul]
      generalize (z - c) * ℓ ^ (j - 1) = w at hMN ⊢
      omega
    omega
  have hpz := powMemSpanPow A (ℓ : A) X (p (j - 1)) (ℓ ^ (j - 1)) (M - r) z c hN1 hp hz
  obtain ⟨α, β, hαβ⟩ := Ideal.mem_span_pair.mp hpz
  have hprod : ∏ s ∈ Finset.range j, (p s ^ (ℓ - 1)) ^ r = (∏ s ∈ Finset.range j, p s ^ E) *
      (p (j - 1) ^ z * ∏ s ∈ (Finset.range j).erase (j - 1), p s ^ z) := by
    rw [Finset.mul_prod_erase (Finset.range j) (fun s => p s ^ z) (Finset.mem_range.mpr (by omega)),
      ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun s _ => ?_
    rw [← pow_mul, ← pow_add, hzd, Nat.add_sub_cancel' hE]
  have hX : X ^ M = X ^ r * X ^ (M - r) := by rw [← pow_add, Nat.add_sub_cancel' hMr.le]
  have hl : (ℓ : A) ^ (r + v) = (ℓ : A) ^ σ * (ℓ : A) ^ c := by
    rw [← pow_add]
    congr 1
    omega
  rw [mul_pow, mul_pow, ← Finset.prod_pow, hprod, ← hαβ]
  convert J.add_mem (J.mul_mem_left (α * u ^ r * (∏ s ∈ (Finset.range j).erase (j - 1), p s ^ z) * X ^ r *
      ∏ s ∈ Finset.range j, p s ^ E) hmem1)
    (J.mul_mem_left (β * u ^ r * (∏ s ∈ (Finset.range j).erase (j - 1), p s ^ z) * (ℓ : A) ^ σ) hmem2) using 1
  rw [hX, hl]
  ring

end Formalism.NOK
