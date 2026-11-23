import Mathlib
open Filter
open scoped Classical

namespace GlobalTheory.LocalGrouping

open Function

theorem ne_zero_of_finprod_mem_ne_zero {ι : Type} (S : Set ι) (h : ι → ℂ)
    (hf : (mulSupport h).Finite) (hne : ∏ᶠ i ∈ S, h i ≠ 0) : ∀ i ∈ S, h i ≠ 0 := by
  intro i hi hzero
  apply hne
  have hfin : (S ∩ mulSupport h).Finite := hf.subset Set.inter_subset_right
  rw [← finprod_mem_inter_mulSupport, finprod_mem_eq_finite_toFinset_prod _ hfin]
  apply Finset.prod_eq_zero (i := i)
  · simp [Set.Finite.mem_toFinset, hi, Function.mem_mulSupport, hzero]
  · exact hzero

theorem finprod_finsum_eq (I : Type) (D : I → Type) (S : Set I) (B : ∀ i, D i → ℂ)
    (T : Finset I) (u : ∀ i, D i) (hTS : (T : Set I) ⊆ S)
    (hfin : ∀ i ∈ S, (support (B i)).Finite)
    (hind : ∀ i ∈ S, i ∉ T → ∀ d, B i d = if d = u i then 1 else 0) :
    ∏ᶠ i ∈ S, ∑ᶠ d, B i d = ∑ᶠ f : (∀ i : T, D i), ∏ i : T, B i (f i) := by
  have hone : ∀ i ∈ S, i ∉ T → ∑ᶠ d, B i d = 1 := by
    intro i hi hT
    rw [finsum_eq_single _ (u i)]
    · simp [hind i hi hT]
    · intro d hd; simp [hind i hi hT, hd]
  rw [finprod_mem_eq_prod_of_subset _ (t := T) ?_ hTS]
  swap
  · rintro i ⟨hiS, hi⟩
    by_contra hT
    exact hi (hone i hiS hT)
  let P : ∀ i : T, Finset (D i) := fun i => (hfin i (hTS i.2)).toFinset
  have hsum : ∀ i : T, ∑ᶠ d, B i d = ∑ d ∈ P i, B i d := fun i =>
    finsum_eq_sum_of_support_subset _ (by simp [P])
  rw [← Finset.prod_coe_sort T, Finset.prod_congr rfl (fun i _ => hsum i), Finset.prod_univ_sum]
  symm
  apply finsum_eq_sum_of_support_subset
  intro f hf
  rw [Function.mem_support, Finset.prod_ne_zero_iff] at hf
  rw [Finset.mem_coe, Fintype.mem_piFinset]
  intro i
  simpa [P] using hf i (Finset.mem_univ _)

end GlobalTheory.LocalGrouping

namespace GlobalTheory.LocalGrouping

open Function

theorem finsum_fibres_eq (I R : Type) (D : I → Type) (S : Set I) (B : ∀ i, D i → ℂ)
    (ℓ : R → ∀ i, D i) (A : Set R) (k m : ℕ)
    (T : Finset I) (u : ∀ i, D i) (hTS : (T : Set I) ⊆ S)
    (hfin : ∀ i ∈ S, (support (B i)).Finite)
    (hind : ∀ i ∈ S, i ∉ T → ∀ d, B i d = if d = u i then 1 else 0)
    (H3 : ∀ c ∈ A, ∀ᶠ i in cofinite, B i (ℓ c i) = 1)
    (H4 : ∀ e : ∀ i, D i, (∀ i ∈ S, B i (e i) ≠ 0) →
      Nat.card {c : R // c ∈ A ∧ ∀ i ∈ S, ℓ c i = e i} * 2 ^ k = 2 ^ m) :
    (∑ᶠ c : R, if c ∈ A then ∏ᶠ i ∈ S, B i (ℓ c i) else 0) * (2 : ℂ) ^ k =
      (2 : ℂ) ^ m * ∑ᶠ f : (∀ i : T, D i), ∏ i : T, B i (f i) := by
  let F : (∀ i : T, D i) → ℂ := fun f => ∏ i : T, B i (f i)
  have hFfin : (support F).Finite := by
    apply (Set.Finite.pi (t := fun i : T => support (B i)) (fun i => hfin i (hTS i.2))).subset
    intro f hf
    rw [mem_support, Finset.prod_ne_zero_iff] at hf
    intro i _
    exact hf i (Finset.mem_univ _)
  let E : (∀ i : T, D i) → ∀ i, D i := fun f i => if h : i ∈ T then f ⟨i, h⟩ else u i
  let Fib : (∀ i : T, D i) → Set R := fun f => {c | c ∈ A ∧ ∀ i ∈ S, ℓ c i = E f i}
  have hEnz : ∀ f, F f ≠ 0 → ∀ i ∈ S, B i (E f i) ≠ 0 := by
    intro f hf i hi
    by_cases hT : i ∈ T
    · simp only [E, hT, dite_true]
      rw [Finset.prod_ne_zero_iff] at hf
      exact hf ⟨i, hT⟩ (Finset.mem_univ _)
    · simp [E, hT, hind i hi hT]
  have hcard : ∀ f, F f ≠ 0 → (Nat.card (Fib f) : ℂ) * 2 ^ k = 2 ^ m := by
    intro f hf
    have h := H4 (E f) (hEnz f hf)
    exact_mod_cast h
  have hFibfin : ∀ f, F f ≠ 0 → (Fib f).Finite := by
    intro f hf
    have h := H4 (E f) (hEnz f hf)
    have hne : Nat.card (Fib f) ≠ 0 := by
      intro h0
      change Nat.card {c : R // c ∈ A ∧ ∀ i ∈ S, ℓ c i = E f i} = 0 at h0
      rw [h0, zero_mul] at h
      exact (pow_ne_zero m two_ne_zero) h.symm
    exact Set.finite_coe_iff.mp (Nat.finite_of_card_ne_zero hne)
  have hpt : ∀ c, (if c ∈ A then ∏ᶠ i ∈ S, B i (ℓ c i) else 0) =
      ∑ f ∈ hFfin.toFinset, if c ∈ Fib f then F f else 0 := by
    intro c
    by_cases hcA : c ∈ A
    swap
    · simp [hcA, Fib]
    rw [if_pos hcA]
    by_cases hex : ∃ f ∈ hFfin.toFinset, c ∈ Fib f
    · obtain ⟨f, hf, hcf⟩ := hex
      rw [Finset.sum_eq_single f]
      · rw [if_pos hcf]
        rw [finprod_mem_eq_prod_of_subset _ (t := T) ?_ hTS]
        · rw [← Finset.prod_coe_sort T]
          apply Finset.prod_congr rfl
          intro i _
          rw [hcf.2 i (hTS i.2)]
          simp [E]
        · rintro i ⟨hiS, hi⟩
          by_contra hT
          apply hi
          show B i (ℓ c i) = 1
          have hT' : i ∉ T := hT
          rw [hcf.2 i hiS]
          simp [E, hT', hind i hiS hT']
      · intro g _ hgf
        rw [if_neg]
        intro hcg
        apply hgf
        funext i
        have h1 := hcf.2 i (hTS i.2)
        have h2 := hcg.2 i (hTS i.2)
        simp [E] at h1 h2
        rw [← h1, ← h2]
      · intro hf'; exact absurd hf hf'
    · rw [Finset.sum_eq_zero]
      swap
      · intro f hf
        rw [if_neg]
        intro hcf; exact hex ⟨f, hf, hcf⟩
      by_contra hne
      have hmf : (mulSupport fun i => B i (ℓ c i)).Finite := Filter.eventually_cofinite.mp (H3 c hcA)
      have hall := ne_zero_of_finprod_mem_ne_zero S _ hmf hne
      apply hex
      refine ⟨fun i => ℓ c i, ?_, hcA, ?_⟩
      · rw [Set.Finite.mem_toFinset, mem_support, Finset.prod_ne_zero_iff]
        intro i _
        exact hall i (hTS i.2)
      · intro i hi
        by_cases hT : i ∈ T
        · simp [E, hT]
        · have := hall i hi
          rw [hind i hi hT] at this
          simp only [E, hT, dite_false]
          by_contra h; exact this (if_neg h)
  have hinner : ∀ f ∈ hFfin.toFinset,
      (∑ᶠ c, if c ∈ Fib f then F f else 0) * (2 : ℂ) ^ k = 2 ^ m * F f := by
    intro f hf
    rw [Set.Finite.mem_toFinset, mem_support] at hf
    have e1 : (∑ᶠ c, if c ∈ Fib f then F f else 0) = ∑ᶠ c ∈ Fib f, F f := by
      rw [finsum_mem_def]
      apply finsum_congr
      intro c
      simp [Set.indicator_apply]
    rw [e1, finsum_mem_eq_finite_toFinset_sum _ (hFibfin f hf), Finset.sum_const,
      ← Nat.card_eq_card_finite_toFinset, nsmul_eq_mul, mul_right_comm, hcard f hf]
  rw [finsum_congr hpt, finsum_sum_comm, Finset.sum_mul, Finset.sum_congr rfl hinner,
    ← Finset.mul_sum]
  · congr 1
    symm
    exact finsum_eq_sum_of_support_subset F (by simp)
  · intro f hf
    rw [Set.Finite.mem_toFinset, mem_support] at hf
    apply (hFibfin f hf).subset
    intro c hc
    by_contra h
    exact hc (if_neg h)

end GlobalTheory.LocalGrouping

namespace GlobalTheory

open Function

theorem finsum_finprod_mul_two_pow_eq :
    ∀ (I R : Type) (D : I → Type) (S : Set I) (B : ∀ i, D i → ℂ) (ℓ : R → ∀ i, D i) (A : Set R)
      (k m : ℕ), (∀ i, Nonempty (D i)) → (∀ i ∈ S, (Function.support (B i)).Finite) →
      (∀ᶠ i in cofinite, ∃ u : D i, ∀ d, B i d = if d = u then 1 else 0) →
      (∀ c ∈ A, ∀ᶠ i in cofinite, B i (ℓ c i) = 1) →
      (∀ e : ∀ i, D i, (∀ i ∈ S, B i (e i) ≠ 0) →
        Nat.card {c : R // c ∈ A ∧ ∀ i ∈ S, ℓ c i = e i} * 2 ^ k = 2 ^ m) →
      (∑ᶠ c : R, if c ∈ A then ∏ᶠ i ∈ S, B i (ℓ c i) else 0) * (2 : ℂ) ^ k =
        (2 : ℂ) ^ m * ∏ᶠ i ∈ S, ∑ᶠ d, B i d := by
  intro I R D S B ℓ A k m H0 H1 H2 H3 H4
  have hbad : {i | ¬ ∃ u : D i, ∀ d, B i d = if d = u then 1 else 0}.Finite :=
    Filter.eventually_cofinite.mp H2
  let T : Finset I := (hbad.inter_of_left S).toFinset
  let u : ∀ i, D i := fun i =>
    if h : ∃ u : D i, ∀ d, B i d = if d = u then 1 else 0 then h.choose else (H0 i).some
  have hTS : (T : Set I) ⊆ S := by
    intro i hi
    simp only [T, Set.Finite.coe_toFinset] at hi
    exact hi.2
  have hind : ∀ i ∈ S, i ∉ T → ∀ d, B i d = if d = u i then 1 else 0 := by
    intro i hi hT
    have hgood : ∃ u : D i, ∀ d, B i d = if d = u then 1 else 0 := by
      by_contra h
      apply hT
      rw [Set.Finite.mem_toFinset]
      exact ⟨h, hi⟩
    intro d
    simp only [u, hgood, dite_true]
    exact hgood.choose_spec d
  rw [LocalGrouping.finprod_finsum_eq I D S B T u hTS H1 hind]
  exact LocalGrouping.finsum_fibres_eq I R D S B ℓ A k m T u hTS H1 hind H3 H4

end GlobalTheory
