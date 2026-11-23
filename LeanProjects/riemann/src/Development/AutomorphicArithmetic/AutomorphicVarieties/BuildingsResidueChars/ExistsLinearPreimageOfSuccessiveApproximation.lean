import Mathlib

theorem UpperTheory.exists_linear_preimage_of_successive_approximation :
    ∀ (A M ι : Type) [CommRing A] [AddCommGroup M] [Module A M] [Fintype ι] (I : Ideal A) [IsAdicComplete I A] (V : ℕ → Submodule A M) (σ : (ι → A) →ₗ[A] M), Antitone V → (∀ k, (I ^ k • ⊤ : Submodule A M) ≤ V k) → (∀ f, (∀ k, f ∈ V k) → f = 0) → (∀ j, ∀ f ∈ V j, ∃ a : ι → A, (∀ i, a i ∈ I ^ j) ∧ f - σ a ∈ V (j + 1)) → ∀ j, ∀ f ∈ V j, ∃ a : ι → A, (∀ i, a i ∈ I ^ j) ∧ σ a = f := by
  intro A M ι _ _ _ _ I _ V σ hV hI hsep hstep j f hf
  classical
  let a' : ℕ → M → ι → A := fun k g => if h : g ∈ V k then (hstep k g h).choose else 0
  have ha' : ∀ k g, g ∈ V k → (∀ i, a' k g i ∈ I ^ k) ∧ g - σ (a' k g) ∈ V (k + 1) := by
    intro k g h
    simp only [a', dif_pos h]
    exact (hstep k g h).choose_spec
  let r : ℕ → M := fun n => Nat.rec f (fun n g => g - σ (a' (j + n) g)) n
  have hrs : ∀ n, r (n + 1) = r n - σ (a' (j + n) (r n)) := fun n => rfl
  have hr : ∀ n, r n ∈ V (j + n) := by
    intro n
    induction n with
    | zero => exact hf
    | succ n ih =>
      rw [hrs, ← add_assoc]
      exact (ha' _ _ ih).2
  let b : ℕ → ι → A := fun n => a' (j + n) (r n)
  have hb : ∀ n i, b n i ∈ I ^ (j + n) := fun n => (ha' _ _ (hr n)).1
  have hrsum : ∀ N, r N = f - σ (∑ n ∈ Finset.range N, b n) := by
    intro N
    induction N with
    | zero => simp [r]
    | succ N ih =>
      show r N - σ (b N) = f - σ (∑ n ∈ Finset.range (N + 1), b n)
      rw [ih, Finset.sum_range_succ, map_add]
      abel
  have hlim : ∀ i, ∃ L : A, ∀ n,
      (∑ k ∈ Finset.range n, b k i) ≡ L [SMOD (I ^ n • ⊤ : Submodule A A)] := by
    intro i
    refine IsPrecomplete.prec (inferInstance : IsPrecomplete I A) ?_
    intro m n hmn
    rw [SModEq.sub_mem, ← neg_sub, Submodule.neg_mem_iff, ← Finset.sum_Ico_eq_sub _ hmn]
    refine Submodule.sum_mem _ (fun k hk => ?_)
    have hmk : m ≤ j + k := by
      have := (Finset.mem_Ico.mp hk).1
      omega
    simpa using Submodule.smul_mem_smul (Ideal.pow_le_pow_right hmk (hb k i))
      (Submodule.mem_top : (1 : A) ∈ (⊤ : Submodule A A))
  choose L hL using hlim
  refine ⟨L, fun i => ?_, ?_⟩
  · have h1 := SModEq.sub_mem.mp (hL i j)
    have h2 : (∑ k ∈ Finset.range j, b k i) ∈ I ^ j :=
      Submodule.sum_mem _ (fun k _ => Ideal.pow_le_pow_right (by omega) (hb k i))
    have h1' : (∑ k ∈ Finset.range j, b k i) - L i ∈ I ^ j := by
      simpa [smul_eq_mul, Ideal.mul_top] using h1
    simpa using Submodule.sub_mem _ h2 h1'
  · have h0 : f - σ L = 0 := by
      apply hsep
      intro N
      have hv : ∀ i, ((∑ n ∈ Finset.range N, b n) - L) i ∈ I ^ N := by
        intro i
        have := SModEq.sub_mem.mp (hL i N)
        simpa [Finset.sum_apply, smul_eq_mul, Ideal.mul_top] using this
      have hσ : σ ((∑ n ∈ Finset.range N, b n) - L) ∈ (I ^ N • ⊤ : Submodule A M) := by
        set v := (∑ n ∈ Finset.range N, b n) - L
        rw [pi_eq_sum_univ v, map_sum]
        refine Submodule.sum_mem _ (fun i _ => ?_)
        rw [map_smul]
        exact Submodule.smul_mem_smul (hv i) Submodule.mem_top
      have e : f - σ L = r N + σ ((∑ n ∈ Finset.range N, b n) - L) := by
        rw [hrsum, map_sub]
        abel
      rw [e]
      exact Submodule.add_mem _ (hV (by omega : N ≤ j + N) (hr N)) (hI N hσ)
    exact (sub_eq_zero.mp h0).symm
