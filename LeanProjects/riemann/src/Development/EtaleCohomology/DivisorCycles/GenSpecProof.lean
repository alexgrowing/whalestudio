import Development.EtaleCohomology.DivisorCycles.CycleCount

open Matrix PositivityTheory.AutomorphicGaloisHodgeTate.Div

namespace LateralTheory.DivDb.GenSpecProof
open LateralTheory.DivDb Finset

variable {C : Type} [Field C] {N n : ℕ}

theorem mem_periodic (π : Equiv.Perm (Fin n)) (k : Fin n) : k ∈ Function.periodicPts π :=
  Function.mk_mem_periodicPts (orderOf_pos π) (by
    show (π^[orderOf π]) k = k
    rw [Equiv.Perm.iterate_eq_pow, pow_orderOf_eq_one]; rfl)

theorem mp_pos (π : Equiv.Perm (Fin n)) (k : Fin n) : 0 < Function.minimalPeriod π k :=
  Function.minimalPeriod_pos_of_mem_periodicPts (mem_periodic π k)

theorem orbit_eq (π : Equiv.Perm (Fin n)) (k : Fin n) :
    (univ.filter (fun m => π.SameCycle k m)) =
      (range (Function.minimalPeriod π k)).image (fun s => (π^[s]) k) := by
  ext m
  simp only [mem_filter, mem_univ, true_and, mem_image, mem_range]
  constructor
  · intro h
    obtain ⟨i, hi⟩ := h.exists_nat_pow_eq
    refine ⟨i % Function.minimalPeriod π k, Nat.mod_lt _ (mp_pos π k), ?_⟩
    rw [Function.iterate_mod_minimalPeriod_eq, Equiv.Perm.iterate_eq_pow, hi]
  · rintro ⟨s, -, rfl⟩
    rw [Equiv.Perm.iterate_eq_pow]
    exact Equiv.Perm.sameCycle_pow_right.2 (Equiv.Perm.SameCycle.refl _ _)

theorem injOn_orbit (π : Equiv.Perm (Fin n)) (k : Fin n) :
    Set.InjOn (fun s => (π^[s]) k) ↑(range (Function.minimalPeriod π k)) := by
  intro a ha b hb h
  exact Function.iterate_injOn_Iio_minimalPeriod (by simpa using ha) (by simpa using hb) h

theorem card_orbit (π : Equiv.Perm (Fin n)) (k : Fin n) :
    (univ.filter (fun m => π.SameCycle k m)).card = Function.minimalPeriod π k := by
  rw [orbit_eq, card_image_of_injOn (injOn_orbit π k), card_range]

theorem prod_orbit (π : Equiv.Perm (Fin n)) (k : Fin n) (τ : Fin n → C) :
    ∏ s ∈ range (Function.minimalPeriod π k), τ ((π^[s]) k) =
      ∏ m ∈ univ.filter (fun m => π.SameCycle k m), τ m := by
  rw [orbit_eq, prod_image (injOn_orbit π k)]

theorem filt_eq (π : Equiv.Perm (Fin n)) {i k : Fin n} (h : π.SameCycle i k) :
    univ.filter (fun m => π.SameCycle i m) = univ.filter (fun m => π.SameCycle k m) := by
  ext m
  simp only [mem_filter, mem_univ, true_and]
  exact ⟨fun h' => h.symm.trans h', fun h' => h.trans h'⟩

theorem tp {p : Fin n → Mat C N} (hp : Sys p) (τ : Fin n → C) (k : Fin n) :
    (∑ j, τ j • p j) * p k = τ k • p k := by
  rw [Finset.sum_mul, Finset.sum_eq_single k]
  · rw [smul_mul_assoc, (hp.1.idem k).eq]
  · intro j _ hj; rw [smul_mul_assoc, hp.1.ortho hj, smul_zero]
  · simp

theorem xpow {p : Fin n → Mat C N} {x : Mat C N} {π : Equiv.Perm (Fin n)}
    (hx : ∀ j, x * p j = p (π j) * x) (m : ℕ) (k : Fin n) :
    x ^ m * p k = p ((π^[m]) k) * x ^ m := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [pow_succ', mul_assoc, ih, ← mul_assoc, hx, mul_assoc, ← pow_succ',
      Function.iterate_succ_apply']

theorem ypow {p : Fin n → Mat C N} {x : Mat C N} {π : Equiv.Perm (Fin n)} (hp : Sys p)
    (hx : ∀ j, x * p j = p (π j) * x) (τ : Fin n → C) (m : ℕ) (k : Fin n) :
    (x * ∑ j, τ j • p j) ^ m * p k = (∏ s ∈ range m, τ ((π^[s]) k)) • (x ^ m * p k) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [pow_succ', mul_assoc, ih, mul_smul_comm, xpow hx, prod_range_succ,
      ← smul_smul, pow_succ', mul_assoc x (x ^ m), xpow hx]
    congr 1
    rw [← mul_assoc, mul_assoc x, tp hp, mul_smul_comm, smul_mul_assoc]
    simp only [mul_assoc]

theorem split {p : Fin n → Mat C N} (hp : Sys p) (O : Finset (Fin n)) (v : Fin N → C)
    (hs : ∀ k, k ∉ O → p k *ᵥ v = 0) (M : Mat C N) : M *ᵥ v = ∑ k ∈ O, (M * p k) *ᵥ v := by
  have h1 : M *ᵥ v = ∑ k, (M * p k) *ᵥ v := by
    conv_lhs => rw [← mul_one M, ← hp.1.complete, Finset.mul_sum]
    rw [Matrix.sum_mulVec]
  rw [h1, ← Finset.sum_subset (subset_univ O)]
  intro k _ hk; rw [← mulVec_mulVec, hs k hk, mulVec_zero]

theorem powv (y : Mat C N) (l : C) (v : Fin N → C) (h : y *ᵥ v = l • v) (m : ℕ) :
    (y ^ m) *ᵥ v = l ^ m • v := by
  induction m with
  | zero => simp
  | succ m ih => rw [pow_succ, ← mulVec_mulVec, h, mulVec_smul, ih, smul_smul, pow_succ']

theorem root_of (M : Mat C N) (β : C) (v : Fin N → C) (hv : v ≠ 0) (h : M *ᵥ v = β • v) :
    M.charpoly.IsRoot β := by
  rw [Polynomial.IsRoot.def, eval_charpoly, ← exists_mulVec_eq_zero_iff]
  refine ⟨v, hv, ?_⟩
  rw [sub_mulVec, h]
  ext a
  simp [Matrix.scalar_apply]

theorem eig {p : Fin n → Mat C N} {x : Mat C N} {π : Equiv.Perm (Fin n)} (hp : Sys p)
    (hxu : IsUnit x) (hx : ∀ j, x * p j = p (π j) * x) (τ : Fin n → C) (hτ : ∀ j, τ j ≠ 0)
    (i : Fin n) (l : C) (v : Fin N → C) (hv : v ≠ 0) (hy : (x * ∑ j, τ j • p j) *ᵥ v = l • v)
    (hs : ∀ k, ¬ π.SameCycle i k → p k *ᵥ v = 0) :
    ∃ β : C, β ≠ 0 ∧ (x ^ (univ.filter (fun m => π.SameCycle i m)).card).charpoly.IsRoot β ∧
      l ^ (univ.filter (fun m => π.SameCycle i m)).card =
        (∏ k ∈ univ.filter (fun m => π.SameCycle i m), τ k) * β := by
  have hs' : ∀ k, k ∉ univ.filter (fun m => π.SameCycle i m) → p k *ᵥ v = 0 :=
    fun k hk => hs k (by simpa using hk)
  have hQ : (∏ k ∈ univ.filter (fun m => π.SameCycle i m), τ k) ≠ 0 :=
    prod_ne_zero_iff.2 fun k _ => hτ k
  have hk : ∀ k ∈ univ.filter (fun m => π.SameCycle i m),
      (x * ∑ j, τ j • p j) ^ (univ.filter (fun m => π.SameCycle i m)).card * p k =
        (∏ k ∈ univ.filter (fun m => π.SameCycle i m), τ k) •
          (x ^ (univ.filter (fun m => π.SameCycle i m)).card * p k) := by
    intro k hk
    have hik : π.SameCycle i k := by simpa using hk
    rw [ypow hp hx]
    congr 1
    rw [filt_eq π hik, card_orbit, prod_orbit]
  have key : (∏ k ∈ univ.filter (fun m => π.SameCycle i m), τ k) •
      (x ^ (univ.filter (fun m => π.SameCycle i m)).card *ᵥ v) =
        l ^ (univ.filter (fun m => π.SameCycle i m)).card • v := by
    rw [← powv _ _ _ hy, split hp _ v hs' (x ^ _),
      split hp _ v hs' ((x * ∑ j, τ j • p j) ^ _), smul_sum]
    refine sum_congr rfl fun k hk' => ?_
    rw [hk k hk', smul_mulVec]
  have hxc := hxu.pow (univ.filter (fun m => π.SameCycle i m)).card
  have hl : l ^ (univ.filter (fun m => π.SameCycle i m)).card ≠ 0 := by
    intro h0
    rw [h0, zero_smul] at key
    have h2 := (smul_eq_zero.1 key).resolve_left hQ
    exact hv ((mulVec_injective_iff_isUnit.2 hxc) (by rw [h2, mulVec_zero]))
  refine ⟨_, div_ne_zero hl hQ, root_of _ _ v hv ?_, by field_simp⟩
  rw [div_eq_inv_mul, ← smul_smul, ← key, smul_smul, inv_mul_cancel₀ hQ, one_smul]

theorem GenSpec_of : GenSpec := by
  intro C _ N n p x π hp hxu hx
  classical
  refine ⟨⋃ a : Fin (n + 1), ⋃ b : Fin (n + 1), Set.image2 (fun β β' => β' ^ (a : ℕ) / β ^ (b : ℕ))
    (↑(x ^ (a : ℕ)).charpoly.roots.toFinset) (↑(x ^ (b : ℕ)).charpoly.roots.toFinset), ?_, ?_⟩
  · exact Set.finite_iUnion fun a => Set.finite_iUnion fun b =>
      (Finset.finite_toSet _).image2 _ (Finset.finite_toSet _)
  intro τ hτ hml i j hij l v w hv hw hyv hyw hsv hsw
  obtain ⟨β, hβ0, hβr, hβ⟩ := eig hp hxu hx τ hτ i l v hv hyv hsv
  obtain ⟨β', hβ0', hβr', hβ'⟩ := eig hp hxu hx τ hτ j l w hw hyw hsw
  have hO : (univ.filter (fun m => π.SameCycle i m)).Nonempty := ⟨i, mem_filter.2 ⟨mem_univ _, Equiv.Perm.SameCycle.refl _ _⟩⟩
  have hO' : (univ.filter (fun m => π.SameCycle j m)).Nonempty := ⟨j, mem_filter.2 ⟨mem_univ _, Equiv.Perm.SameCycle.refl _ _⟩⟩
  have hd : Disjoint (univ.filter (fun m => π.SameCycle i m)) (univ.filter (fun m => π.SameCycle j m)) := by
    rw [Finset.disjoint_left]
    intro m h1 h2
    simp only [mem_filter, mem_univ, true_and] at h1 h2
    exact hij (h1.trans h2.symm)
  have hc : ∀ O : Finset (Fin n), O.card < n + 1 := fun O =>
    Nat.lt_succ_of_le ((card_le_univ O).trans (by simp))
  refine hml _ _ hO hO' hd (β' ^ (univ.filter (fun m => π.SameCycle i m)).card /
    β ^ (univ.filter (fun m => π.SameCycle j m)).card) ?_ ?_
  · refine Set.mem_iUnion.2 ⟨⟨_, hc (univ.filter (fun m => π.SameCycle i m))⟩, Set.mem_iUnion.2
      ⟨⟨_, hc (univ.filter (fun m => π.SameCycle j m))⟩, Set.mem_image2_of_mem ?_ ?_⟩⟩
    · simp only [Finset.mem_coe, Multiset.mem_toFinset]
      exact (Polynomial.mem_roots (Matrix.charpoly_monic _).ne_zero).2 hβr
    · simp only [Finset.mem_coe, Multiset.mem_toFinset]
      exact (Polynomial.mem_roots (Matrix.charpoly_monic _).ne_zero).2 hβr'
  · rw [div_mul_eq_mul_div, eq_div_iff (pow_ne_zero _ hβ0), ← mul_pow, ← hβ, ← pow_mul,
      ← mul_pow, mul_comm β', ← hβ', ← pow_mul, mul_comm]

end LateralTheory.DivDb.GenSpecProof
