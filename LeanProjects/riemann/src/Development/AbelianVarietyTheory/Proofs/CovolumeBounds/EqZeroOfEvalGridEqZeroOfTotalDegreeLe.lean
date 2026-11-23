import Mathlib

namespace GlobalTheory

open MvPolynomial

section Vanishing

variable {σ R : Type*} [Finite σ] [CommRing R] [IsDomain R] [CharZero R]

theorem eq_zero_of_eval_box_eq_zero (d : σ → ℕ) (P : MvPolynomial σ R)
    (hdeg : ∀ i, P.degreeOf i ≤ d i)
    (hP : ∀ x : σ → ℕ, (∀ i, x i ≤ d i) → eval (fun i => (x i : R)) P = 0) : P = 0 := by
  classical
  refine eq_zero_of_eval_zero_at_prod_finset P
    (fun i => (Finset.range (d i + 1)).image (Nat.cast : ℕ → R)) (fun i => ?_) (fun x hx => ?_)
  · rw [Finset.card_image_of_injective _ Nat.cast_injective, Finset.card_range]
    exact Nat.lt_succ_of_le (hdeg i)
  · choose n hn hnx using fun i => Finset.mem_image.1 (hx i)
    have : x = fun i => (n i : R) := funext fun i => (hnx i).symm
    rw [this]
    exact hP n fun i => Nat.lt_succ_iff.1 (Finset.mem_range.1 (hn i))

theorem eq_zero_of_eval_grid_eq_zero (d : ℕ) (P : MvPolynomial σ R)
    (hdeg : ∀ i, P.degreeOf i ≤ d)
    (hP : ∀ x : σ → ℕ, (∀ i, x i ≤ d) → eval (fun i => (x i : R)) P = 0) : P = 0 :=
  eq_zero_of_eval_box_eq_zero (fun _ => d) P hdeg hP

end Vanishing

section Span

variable {σ A K V : Type*} [Finite σ] [Field K] [CharZero K] [CommSemiring A] [Algebra A K]
  [AddCommGroup V] [Module K V]

theorem mem_of_grid_mem (d : ℕ) (Φ : (σ → A) → V)
    (hΦ : ∀ l : Module.Dual K V, ∃ P : MvPolynomial σ K, (∀ i, P.degreeOf i ≤ d) ∧
      ∀ x, l (Φ x) = eval (fun i => algebraMap A K (x i)) P)
    (U : Submodule K V)
    (hU : ∀ x : σ → ℕ, (∀ i, x i ≤ d) → Φ (fun i => (x i : A)) ∈ U) (y : σ → A) :
    Φ y ∈ U := by
  rw [← Subspace.forall_mem_dualAnnihilator_apply_eq_zero_iff U]
  intro l hl
  obtain ⟨P, hdeg, hP⟩ := hΦ l
  have h0 : P = 0 := by
    refine eq_zero_of_eval_grid_eq_zero d P hdeg fun x hx => ?_
    have := (Submodule.mem_dualAnnihilator l).1 hl _ (hU x hx)
    rw [hP] at this
    simpa using this
  rw [hP, h0, map_zero]

theorem span_grid_eq_span_range (d : ℕ) (Φ : (σ → A) → V)
    (hΦ : ∀ l : Module.Dual K V, ∃ P : MvPolynomial σ K, (∀ i, P.degreeOf i ≤ d) ∧
      ∀ x, l (Φ x) = eval (fun i => algebraMap A K (x i)) P) :
    Submodule.span K ((fun x : σ → ℕ => Φ fun i => (x i : A)) '' {x | ∀ i, x i ≤ d}) =
      Submodule.span K (Set.range Φ) := by
  apply le_antisymm
  · apply Submodule.span_mono
    rintro _ ⟨x, -, rfl⟩
    exact ⟨_, rfl⟩
  · rw [Submodule.span_le]
    rintro _ ⟨y, rfl⟩
    refine mem_of_grid_mem d Φ hΦ _ (fun x hx => ?_) y
    apply Submodule.subset_span
    exact ⟨x, hx, rfl⟩

omit [Finite σ] [CharZero K] in

theorem exists_poly_dual_sum_monomial_smul (d : ℕ) (s : Finset (σ →₀ ℕ)) (v : (σ →₀ ℕ) → V)
    (hs : ∀ a ∈ s, ∀ i, a i ≤ d) (l : Module.Dual K V) :
    ∃ P : MvPolynomial σ K, (∀ i, P.degreeOf i ≤ d) ∧ ∀ x : σ → A,
      l (∑ a ∈ s, (a.prod fun i n => algebraMap A K (x i) ^ n) • v a) =
        eval (fun i => algebraMap A K (x i)) P := by
  classical
  refine ⟨∑ a ∈ s, monomial a (l (v a)), fun i => ?_, fun x => ?_⟩
  · rw [degreeOf_le_iff]
    intro m hm
    obtain ⟨a, ha, hma⟩ := Finset.mem_biUnion.1 (support_sum hm)
    have := Finset.mem_singleton.1 (support_monomial_subset hma)
    rw [this]
    exact hs a ha i
  · simp only [map_sum, map_smul, eval_monomial, smul_eq_mul, mul_comm]

theorem span_grid_eq_span_range_of_eq_sum (d : ℕ) (Φ : (σ → A) → V)
    (s : Finset (σ →₀ ℕ)) (v : (σ →₀ ℕ) → V) (hs : ∀ a ∈ s, ∀ i, a i ≤ d)
    (hΦ : ∀ x, Φ x = ∑ a ∈ s, (a.prod fun i n => algebraMap A K (x i) ^ n) • v a) :
    Submodule.span K ((fun x : σ → ℕ => Φ fun i => (x i : A)) '' {x | ∀ i, x i ≤ d}) =
      Submodule.span K (Set.range Φ) := by
  refine span_grid_eq_span_range d Φ fun l => ?_
  simp only [hΦ]
  exact exists_poly_dual_sum_monomial_smul d s v hs l

theorem span_grid_eval_eq_span_range {B : Type*} [CommRing B] [Algebra K B] (d : ℕ)
    (F : MvPolynomial σ B) (hF : ∀ i, F.degreeOf i ≤ d) :
    Submodule.span K ((fun x : σ → ℕ => eval (fun i => (x i : B)) F) '' {x | ∀ i, x i ≤ d}) =
      Submodule.span K (Set.range fun x : σ → A =>
        eval (fun i => algebraMap K B (algebraMap A K (x i))) F) := by
  have h := span_grid_eq_span_range_of_eq_sum (K := K) d
    (fun x : σ → A => eval (fun i => algebraMap K B (algebraMap A K (x i))) F)
    F.support (fun a => F.coeff a) (fun a ha i => (degreeOf_le_iff.1 (hF i)) a ha)
    (fun x => by
      rw [eval_eq]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [Algebra.smul_def, Finsupp.prod, map_prod, mul_comm]
      simp only [map_pow])
  simpa only [map_natCast] using h

end Span

section Combination

variable {ι κ V : Type*} [Fintype ι] [AddCommGroup V] {W : ι → Type*}
  [∀ j, AddCommGroup (W j)]

theorem exists_nsmul_add_apply_ne_zero [∀ j, IsAddTorsionFree (W j)] (l : ∀ j, V →+ W j)
    (v w : V) :
    ∃ c : ℕ, c ≤ Fintype.card ι ∧ ∀ j, l j v ≠ 0 ∨ l j w ≠ 0 → l j (c • w + v) ≠ 0 := by
  classical
  by_contra h
  push Not at h
  choose f hf hf0 using h
  have hinj : Function.Injective fun a : Fin (Fintype.card ι + 1) =>
      f a (Nat.lt_succ_iff.1 a.2) := by
    intro a b hab
    have h1 := hf0 a (Nat.lt_succ_iff.1 a.2)
    have h2 := hf0 b (Nat.lt_succ_iff.1 b.2)
    have h3 := hf a (Nat.lt_succ_iff.1 a.2)
    simp only at hab
    rw [← hab] at h2
    generalize f a _ = j at h1 h2 h3
    rw [map_add, map_nsmul] at h1 h2
    have hw : l j w ≠ 0 := by
      intro hw
      rw [hw, nsmul_zero, zero_add] at h1
      exact h3.elim (· h1) (· hw)
    have h4 : (a : ℕ) • l j w = (b : ℕ) • l j w := add_right_cancel (h1.trans h2.symm)
    have h5 : ((a : ℤ) - (b : ℤ)) • l j w = 0 := by
      rw [sub_smul, natCast_zsmul, natCast_zsmul, h4, sub_self]
    have h6 := (smul_eq_zero.1 h5).resolve_right hw
    exact Fin.ext (by omega)
  have := Fintype.card_le_of_injective _ hinj
  simp at this

theorem exists_sum_nsmul_apply_ne_zero_finset [∀ j, IsAddTorsionFree (W j)]
    (l : ∀ j, V →+ W j) (s : κ → V) (t : Finset κ) :
    ∃ c : κ → ℕ, (∀ k, c k ≤ Fintype.card ι) ∧
      ∀ j, (∃ k ∈ t, l j (s k) ≠ 0) → l j (∑ k ∈ t, c k • s k) ≠ 0 := by
  classical
  induction t using Finset.induction_on with
  | empty => exact ⟨0, fun _ => Nat.zero_le _, fun j ⟨k, hk, _⟩ => absurd hk (by simp)⟩
  | insert a t ha ih =>
    obtain ⟨c, hc, hl⟩ := ih
    obtain ⟨n, hn, hln⟩ := exists_nsmul_add_apply_ne_zero l (∑ k ∈ t, c k • s k) (s a)
    refine ⟨Function.update c a n, fun k => ?_, fun j ⟨k, hk, hjk⟩ => ?_⟩
    · by_cases hk : k = a
      · subst hk; simpa using hn
      · simpa [hk] using hc k
    · rw [Finset.sum_insert ha, Function.update_self,
        Finset.sum_congr rfl (g := fun k => c k • s k) fun k hk => by
          rw [Function.update_of_ne (ne_of_mem_of_not_mem hk ha)]]
      apply hln
      rcases Finset.mem_insert.1 hk with rfl | hk
      · exact Or.inr hjk
      · exact Or.inl (hl j ⟨k, hk, hjk⟩)

theorem exists_sum_nsmul_apply_ne_zero [∀ j, IsAddTorsionFree (W j)] [Fintype κ]
    (l : ∀ j, V →+ W j) (s : κ → V) (h : ∀ j, ∃ k, l j (s k) ≠ 0) :
    ∃ c : κ → ℕ, (∀ k, c k ≤ Fintype.card ι) ∧ ∀ j, l j (∑ k, c k • s k) ≠ 0 := by
  obtain ⟨c, hc, hl⟩ := exists_sum_nsmul_apply_ne_zero_finset l s Finset.univ
  exact ⟨c, hc, fun j => hl j ((h j).imp fun k hk => ⟨Finset.mem_univ k, hk⟩)⟩

variable {K : Type*} [Field K] [CharZero K] [Module K V] [∀ j, Module K (W j)]

theorem exists_sum_natCast_smul_apply_ne_zero [Fintype κ]
    (l : ∀ j, V →ₗ[K] W j) (s : κ → V) (h : ∀ j, ∃ k, l j (s k) ≠ 0) :
    ∃ c : κ → ℕ, (∀ k, c k ≤ Fintype.card ι) ∧ ∀ j, l j (∑ k, (c k : K) • s k) ≠ 0 := by
  have : ∀ j, IsAddTorsionFree (W j) := fun j => IsAddTorsionFree.of_isTorsionFree K (W j)
  simp only [Nat.cast_smul_eq_nsmul]
  exact exists_sum_nsmul_apply_ne_zero (fun j => (l j).toAddMonoidHom) s h

end Combination

end GlobalTheory
