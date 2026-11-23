import Mathlib

namespace GlobalTheory.OrdMul

open MvPolynomial

theorem coeff_mem_of_mul {O : Type} [CommRing O] (I : Ideal O) {ι : Type} (K : Set ι) (q : ι)
    (hq : q ∉ K) (a F : MvPolynomial ι O) (N : ℕ) (h0 : a.coeff 0 = 0)
    (hu : IsUnit (a.coeff (Finsupp.single q 1)))
    (H : ∀ m : ι →₀ ℕ, m.degree < N + 1 → (∀ j ∈ K, m j = 0) → (a * F).coeff m ∈ I) :
    ∀ m : ι →₀ ℕ, m.degree < N → (∀ j ∈ K, m j = 0) → F.coeff m ∈ I := by
  classical

  have key : ∀ n : ℕ, ∀ m : ι →₀ ℕ, m q + 2 * (m.erase q).degree = n → m.degree < N →
      (∀ j ∈ K, m j = 0) → F.coeff m ∈ I := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro m hμ hm hK
      set m' : ι →₀ ℕ := m + Finsupp.single q 1 with hm'
      have hdeg' : m'.degree < N + 1 := by
        rw [hm', map_add, Finsupp.degree_single]; omega
      have hK' : ∀ j ∈ K, m' j = 0 := by
        intro j hj
        have hqj : q ≠ j := fun h => hq (h ▸ hj)
        simp [hm', hK j hj, Finsupp.single_apply, hqj]
      have hH := H m' hdeg' hK'
      rw [MvPolynomial.coeff_mul] at hH
      have hmem : (Finsupp.single q 1, m) ∈ Finset.HasAntidiagonal.antidiagonal m' := by
        rw [Finset.HasAntidiagonal.mem_antidiagonal, hm']; exact add_comm _ _
      rw [← Finset.add_sum_erase _ _ hmem] at hH
      have hrest : ∑ x ∈ (Finset.HasAntidiagonal.antidiagonal m').erase (Finsupp.single q 1, m),
          a.coeff x.1 * F.coeff x.2 ∈ I := by
        refine Ideal.sum_mem _ (fun x hx => ?_)
        obtain ⟨hne, hx⟩ := Finset.mem_erase.mp hx
        rw [Finset.HasAntidiagonal.mem_antidiagonal] at hx
        by_cases hi : x.1 = 0
        · rw [hi, h0, zero_mul]; exact I.zero_mem
        · apply I.mul_mem_left
          have hiq : x.1 ≠ Finsupp.single q 1 := by
            intro h
            apply hne
            refine Prod.ext h ?_
            rw [h, hm', add_comm m] at hx
            exact add_left_cancel hx
          have hxq : x.1 q + x.2 q = m q + 1 := by
            have := congrArg (fun f : ι →₀ ℕ => f q) hx
            simpa [hm'] using this
          have hxe : x.1.erase q + x.2.erase q = m.erase q := by
            have := congrArg (Finsupp.erase q) hx
            simpa [hm', Finsupp.erase_add] using this
          have hD : (x.1.erase q).degree + (x.2.erase q).degree = (m.erase q).degree := by
            rw [← map_add, hxe]
          have hdx : x.1.degree + x.2.degree = m.degree + 1 := by
            have := congrArg Finsupp.degree hx
            simpa [hm'] using this
          have hd1 : x.1.degree ≠ 0 := fun h => hi ((Finsupp.degree_eq_zero_iff _).mp h)

          have hw : 2 ≤ x.1 q + 2 * (x.1.erase q).degree := by
            by_cases he : x.1.erase q = 0
            · have hs : Finsupp.single q (x.1 q) = x.1 := by
                simpa [he] using Finsupp.single_add_erase q x.1
              have h0' : x.1 q ≠ 0 := by
                intro h; apply hi; rw [← hs, h, Finsupp.single_zero]
              have h1' : x.1 q ≠ 1 := by
                intro h; apply hiq; rw [← hs, h]
              omega
            · have : (x.1.erase q).degree ≠ 0 := fun h => he ((Finsupp.degree_eq_zero_iff _).mp h)
              omega
          refine ih (x.2 q + 2 * (x.2.erase q).degree) (by omega) x.2 rfl (by omega) ?_
          intro j hj
          have h1 := hK' j hj
          rw [← hx] at h1
          simp only [Finsupp.add_apply] at h1
          omega
      have hmain : a.coeff (Finsupp.single q 1) * F.coeff m ∈ I :=
        (Ideal.add_mem_iff_left I hrest).mp hH
      exact (Ideal.unit_mul_mem_iff_mem I hu).mp hmain
  exact fun m hm hK => key _ m rfl hm hK

theorem coeff_mem_of_pow_mul : ∀ (O : Type) [CommRing O] (I : Ideal O) (ι : Type) (K : Set ι) (q : ι), q ∉ K → ∀ (a F : MvPolynomial ι O) (N k : ℕ), a.coeff 0 = 0 → IsUnit (a.coeff (Finsupp.single q 1)) → (∀ m : ι →₀ ℕ, m.degree < N + k → (∀ j ∈ K, m j = 0) → (a ^ k * F).coeff m ∈ I) → ∀ m : ι →₀ ℕ, m.degree < N → (∀ j ∈ K, m j = 0) → F.coeff m ∈ I := by
  intro O _ I ι K q hq a F N k h0 hu H
  induction k generalizing F N with
  | zero =>
    intro m hm hK
    simpa using H m (by simpa using hm) hK
  | succ k ih =>
    refine coeff_mem_of_mul I K q hq a F N h0 hu ?_
    refine ih (a * F) (N + 1) ?_
    intro m hm hK
    have := H m (by omega) hK
    rwa [pow_succ, mul_assoc] at this

end GlobalTheory.OrdMul
