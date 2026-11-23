import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.WittOnFalse
import Development.AbelianVarietyTheory.Definitions.Divisors.FormalCoboundarySmul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PowerSeriesEvalTwoGroupsRules

set_option autoImplicit false

noncomputable section

open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz

namespace GlobalTheory.Katz.CocRel

variable {R : Type} [CommRing R] {d : ℕ} {τ : Type}

abbrev ex3 (a b c : ℕ) : Fin 3 →₀ ℕ :=
  Finsupp.single (0 : Fin 3) a + Finsupp.single 1 b + Finsupp.single 2 c

theorem threeVariableMonomialExponent_eq_iff (a b c a' b' c' : ℕ) : ex3 a b c = ex3 a' b' c' ↔ a' = a ∧ b' = b ∧ c' = c := by
  constructor
  · intro h
    have h0 := DFunLike.congr_fun h 0
    have h1 := DFunLike.congr_fun h 1
    have h2 := DFunLike.congr_fun h 2
    simp at h0 h1 h2
    exact ⟨h0.symm, h1.symm, h2.symm⟩
  · rintro ⟨rfl, rfl, rfl⟩; rfl

theorem coeff_mono3 (a b c i j l : ℕ) (r : ℕ) :
    coeff (R := R) (ex3 i j l) (X 0 ^ a * X 1 ^ b * X 2 ^ c * (r : MvPowerSeries (Fin 3) R)) =
      if a = i ∧ b = j ∧ c = l then (r : R) else 0 := by
  rw [← map_natCast (C : R →+* MvPowerSeries (Fin 3) R), coeff_mul_C, X_pow_eq, X_pow_eq, X_pow_eq,
    monomial_mul_monomial, monomial_mul_monomial, coeff_monomial]
  have := threeVariableMonomialExponent_eq_iff i j l a b c
  by_cases h : a = i ∧ b = j ∧ c = l
  · rw [if_pos (this.2 h), if_pos h]; simp
  · rw [if_neg (fun h' => h (this.1 h')), if_neg h, zero_mul]

theorem coeff_left (p q i j l : ℕ) :
    coeff (ex3 i j l) ((X 0 + X 1) ^ p * X 2 ^ q : MvPowerSeries (Fin 3) R) =
      if p = i + j ∧ q = l then (p.choose i : R) else 0 := by
  rw [add_pow, Finset.sum_mul, map_sum]
  simp only [mul_right_comm _ (_ : MvPowerSeries (Fin 3) R) (X 2 ^ q)]
  have h : ∀ k, coeff (R := R) (ex3 i j l) (X 0 ^ k * X 2 ^ q * X 1 ^ (p - k) * ((p.choose k : ℕ) :
      MvPowerSeries (Fin 3) R)) = if k = i ∧ p - k = j ∧ q = l then (p.choose k : R) else 0 := by
    intro k
    rw [← coeff_mono3, mul_right_comm (X 0 ^ k)]
  simp only [h]
  rw [Finset.sum_eq_single i]
  · by_cases hp : i ≤ p
    · exact if_congr (by omega) rfl rfl
    · rw [Nat.choose_eq_zero_of_lt (by omega)]; simp
  · intro k _ hk
    exact if_neg fun h' => hk h'.1
  · intro hi
    rw [Nat.choose_eq_zero_of_lt (by simpa using hi)]; simp

theorem coeff_right (p q i j l : ℕ) :
    coeff (ex3 i j l) (X 0 ^ p * (X 1 + X 2) ^ q : MvPowerSeries (Fin 3) R) =
      if p = i ∧ q = j + l then (q.choose j : R) else 0 := by
  rw [add_pow, Finset.mul_sum, map_sum]
  simp only [← mul_assoc, coeff_mono3]
  rw [Finset.sum_eq_single j]
  · by_cases hp : j ≤ q
    · exact if_congr (by omega) rfl rfl
    · rw [Nat.choose_eq_zero_of_lt (by omega)]; simp
  · intro k _ hk
    exact if_neg fun h' => hk h'.2.1
  · intro hi
    rw [Nat.choose_eq_zero_of_lt (by simpa using hi)]; simp

theorem coeff_yz (p q i j l : ℕ) :
    coeff (ex3 i j l) (X 1 ^ p * X 2 ^ q : MvPowerSeries (Fin 3) R) =
      if 0 = i ∧ p = j ∧ q = l then 1 else 0 := by
  simpa using coeff_mono3 (R := R) 0 p q i j l 1

theorem coeff_xy (p q i j l : ℕ) :
    coeff (ex3 i j l) (X 0 ^ p * X 1 ^ q : MvPowerSeries (Fin 3) R) =
      if p = i ∧ q = j ∧ 0 = l then 1 else 0 := by
  simpa using coeff_mono3 (R := R) p q 0 i j l 1

theorem coeff_powerSeriesEvalTwoGroups_piSingle (c : MvPowerSeries (Fin d ⊕ Fin d) R) (m : Fin d)
    {A B : MvPowerSeries τ R} (hA : constantCoeff A = 0) (hB : constantCoeff B = 0)
    (e : τ →₀ ℕ) (p q : ℕ) (h : ∀ p' q', ¬ (p' = p ∧ q' = q) → coeff e (A ^ p' * B ^ q') = 0) :
    coeff e (at2 c (Pi.single m A) (Pi.single m B)) =
      coeff (Finsupp.single (Sum.inl m) p + Finsupp.single (Sum.inr m) q) c *
        coeff e (A ^ p * B ^ q) := by
  have h0 : ∀ {A : MvPowerSeries τ R}, constantCoeff A = 0 → ∀ i,
      constantCoeff ((Pi.single m A : Fin d → MvPowerSeries τ R) i) = 0 := by
    intro A hA i
    by_cases hi : i = m
    · subst hi; simpa using hA
    · simp [hi]
  have hs := SubstCalc.hasSubst_elim (h0 hA) (h0 hB)
  have hprod : ∀ p' q', (Finsupp.single (Sum.inl m) p' + Finsupp.single (Sum.inr m) q' :
      Fin d ⊕ Fin d →₀ ℕ).prod (fun s k => (Sum.elim (Pi.single m A) (Pi.single m B) s :
        MvPowerSeries τ R) ^ k) = A ^ p' * B ^ q' := by
    intro p' q'
    rw [Finsupp.prod_add_index' (fun _ => pow_zero _) (fun _ _ _ => pow_add _ _ _),
      Finsupp.prod_single_index (by exact pow_zero _),
      Finsupp.prod_single_index (by exact pow_zero _)]
    simp
  unfold at2
  rw [coeff_subst hs,
    finsum_eq_single _ (Finsupp.single (Sum.inl m) p + Finsupp.single (Sum.inr m) q), hprod,
    smul_eq_mul]
  intro δ hδ
  by_cases hc : δ = Finsupp.single (Sum.inl m) (δ (Sum.inl m)) +
      Finsupp.single (Sum.inr m) (δ (Sum.inr m))
  · rw [congrArg (fun δ' : Fin d ⊕ Fin d →₀ ℕ => δ'.prod _) hc, hprod, h, smul_zero]
    rintro ⟨h1, h2⟩
    rw [h1, h2] at hc
    exact hδ hc
  · obtain ⟨s, hs'⟩ : ∃ s, δ s ≠ (Finsupp.single (Sum.inl m) (δ (Sum.inl m)) +
      Finsupp.single (Sum.inr m) (δ (Sum.inr m)) : Fin d ⊕ Fin d →₀ ℕ) s := by
      by_contra hh
      exact hc (Finsupp.ext fun s => by_contra fun h' => hh ⟨s, h'⟩)
    have key : δ s ≠ 0 ∧ (Sum.elim (Pi.single m A) (Pi.single m B) s : MvPowerSeries τ R) = 0 := by
      rcases s with t | t <;> by_cases ht : t = m
      · subst ht; simp at hs'
      · simpa [ht, Finsupp.single_apply, Ne.symm ht] using hs'
      · subst ht; simp at hs'
      · simpa [ht, Finsupp.single_apply, Ne.symm ht] using hs'
    rw [Finsupp.prod, Finset.prod_eq_zero (Finsupp.mem_support_iff.2 key.1)
      (by rw [key.2, zero_pow key.1]), map_zero, smul_zero]

theorem cocycle_at (c : MvPowerSeries (Fin d ⊕ Fin d) R) (hc : cob2 (addLaw R d) c = 0)
    {u v t : Fin d → MvPowerSeries τ R} (hu : ∀ i, constantCoeff (u i) = 0)
    (hv : ∀ i, constantCoeff (v i) = 0) (ht : ∀ i, constantCoeff (t i) = 0) :
    at2 c v t - at2 c (u + v) t + at2 c u (v + t) - at2 c u v = 0 := by
  set w : Fin d ⊕ (Fin d ⊕ Fin d) → MvPowerSeries τ R := Sum.elim u (Sum.elim v t) with hw
  have hw0 : ∀ s, constantCoeff (w s) = 0 := fun s => by
    rcases s with s | s | s <;> simp [hw, hu, hv, ht]
  have hsw : HasSubst w := hasSubst_of_constantCoeff_zero hw0
  have h1 : ∀ i, subst w (x1 (R := R) (d := d) i) = u i := fun i => by
    unfold x1; rw [subst_X hsw]; rfl
  have h2 : ∀ i, subst w (x2 (R := R) (d := d) i) = v i := fun i => by
    unfold x2; rw [subst_X hsw]; rfl
  have h3 : ∀ i, subst w (x3 (R := R) (d := d) i) = t i := fun i => by
    unfold x3; rw [subst_X hsw]; rfl
  have hx0 : ∀ i, constantCoeff (x1 (R := R) (d := d) i) = 0 := fun i => constantCoeff_X _
  have hx20 : ∀ i, constantCoeff (x2 (R := R) (d := d) i) = 0 := fun i => constantCoeff_X _
  have hx30 : ∀ i, constantCoeff (x3 (R := R) (d := d) i) = 0 := fun i => constantCoeff_X _
  have hop : ∀ (a b : Fin d → MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) R),
      (∀ i, constantCoeff (a i) = 0) → (∀ i, constantCoeff (b i) = 0) →
      op (addLaw R d) a b = a + b := by
    intro a b ha hb
    funext i
    unfold op addLaw at2
    have := SubstCalc.hasSubst_elim ha hb
    rw [subst_add this, subst_X this, subst_X this]
    rfl
  have hop0 : ∀ (a b : Fin d → MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) R),
      (∀ i, constantCoeff (a i) = 0) → (∀ i, constantCoeff (b i) = 0) →
      ∀ i, constantCoeff ((a + b) i) = 0 := by
    intro a b ha hb i; simp [ha, hb]
  have key := congrArg (subst w) hc
  unfold cob2 at key
  rw [hop _ _ hx0 hx20, hop _ _ hx20 hx30] at key
  rw [subst_sub hsw, subst_add hsw, subst_sub hsw,
    SubstCalc.subst_powerSeriesEvalTwoGroups hx20 hx30 hw0, SubstCalc.subst_powerSeriesEvalTwoGroups (hop0 _ _ hx0 hx20) hx30 hw0,
    SubstCalc.subst_powerSeriesEvalTwoGroups hx0 (hop0 _ _ hx20 hx30) hw0, SubstCalc.subst_powerSeriesEvalTwoGroups hx0 hx20 hw0] at key
  have e : ∀ (a b : Fin d → MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) R),
      (fun i => subst w ((a + b) i)) = (fun i => subst w (a i)) + (fun i => subst w (b i)) := by
    intro a b; funext i; simp only [Pi.add_apply]; exact subst_add hsw _ _
  rw [e, e] at key
  simp only [h1, h2, h3] at key
  have e0 : subst w (0 : MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) R) = 0 := by
    simpa using (subst_sub hsw (0 : MvPowerSeries _ R) 0)
  rw [e0] at key
  convert key using 2

theorem relations : ∀ (R : Type) [CommRing R] (d : ℕ) (c : MvPowerSeries (Fin d ⊕ Fin d) R), cob2 (addLaw R d) c = 0 → ∀ m : Fin d, (∀ n, 0 < n → coeff (Finsupp.single (Sum.inl m) n) c = 0) ∧ ∀ i j l, 0 < i → 0 < j → 0 < l → coeff (Finsupp.single (Sum.inl m) (i + j) + Finsupp.single (Sum.inr m) l) c * ((i + j).choose i : R) = coeff (Finsupp.single (Sum.inl m) i + Finsupp.single (Sum.inr m) (j + l)) c * ((j + l).choose j : R) := by
  intro R _ d c hc m
  have h0 : ∀ (k : Fin 3) i,
      constantCoeff ((Pi.single m (X k) : Fin d → MvPowerSeries (Fin 3) R) i) = 0 := by
    intro k i
    by_cases hi : i = m
    · subst hi; simp
    · simp [hi]
  have hid := cocycle_at c hc (h0 0) (h0 1) (h0 2)
  rw [← Pi.single_add, ← Pi.single_add] at hid
  have key : ∀ i j l : ℕ, 0 < i →
      - coeff (Finsupp.single (Sum.inl m) (i + j) + Finsupp.single (Sum.inr m) l) c *
        ((i + j).choose i : R) +
      coeff (Finsupp.single (Sum.inl m) i + Finsupp.single (Sum.inr m) (j + l)) c *
        ((j + l).choose j : R) -
      coeff (Finsupp.single (Sum.inl m) i + Finsupp.single (Sum.inr m) j) c *
        (if 0 = l then 1 else 0) = 0 := by
    intro i j l hi
    have h := congrArg (coeff (ex3 i j l)) hid
    rw [map_sub, map_add, map_sub, map_zero,
      coeff_powerSeriesEvalTwoGroups_piSingle c m (by simp) (by simp) _ j l
        (fun p q hpq => by rw [coeff_yz, if_neg (by omega)]),
      coeff_powerSeriesEvalTwoGroups_piSingle c m (by simp) (by simp) _ (i + j) l
        (fun p q hpq => by rw [coeff_left, if_neg hpq]),
      coeff_powerSeriesEvalTwoGroups_piSingle c m (by simp) (by simp) _ i (j + l)
        (fun p q hpq => by rw [coeff_right, if_neg hpq]),
      coeff_powerSeriesEvalTwoGroups_piSingle c m (by simp) (by simp) _ i j
        (fun p q hpq => by rw [coeff_xy, if_neg (by omega)]),
      coeff_yz, coeff_left, coeff_right, coeff_xy, if_neg (by omega), if_pos ⟨rfl, rfl⟩,
      if_pos ⟨rfl, rfl⟩] at h
    simp only [true_and] at h
    linear_combination h
  refine ⟨fun n hn => ?_, fun i j l hi _ hl => ?_⟩
  · simpa using key n 0 0 hn
  · have h := key i j l hi
    rw [if_neg (by omega)] at h
    linear_combination -h

end GlobalTheory.Katz.CocRel
