import Mathlib

open Polynomial

namespace GlobalTheory

theorem mem_pow_of_jets_vanish (k A : Type) [Field k] [IsAlgClosed k] [CharZero k] [CommRing A]
    [IsDedekindDomain A] [Algebra k A] [Algebra.FiniteType k A] (N : ℕ) (Δ : ℕ → A →ₗ[k] k)
    (hN : 2 ≤ N) (h01 : Δ 0 1 = 1)
    (hL : ∀ l < N, ∀ u w : A, Δ l (u * w) =
      ∑ p ∈ Finset.range (l + 1), l.choose p • (Δ p u * Δ (l - p) w))
    (hπ : ∃ π : A, Δ 1 π = 1) :
    ∃ Q : Ideal A, Q.IsMaximal ∧ (∀ u, u ∈ Q ↔ Δ 0 u = 0) ∧
      ∀ f : A, (∀ l < N, Δ l f = 0) → f ∈ Q ^ N := by
  obtain ⟨π, hπ⟩ := hπ
  have hN0 : 0 < N := by omega
  have hN1 : 1 < N := by omega
  have hmul0 : ∀ u w : A, Δ 0 (u * w) = Δ 0 u * Δ 0 w := by
    intro u w; rw [hL 0 hN0]; simp
  have halg : ∀ c : k, Δ 0 (algebraMap k A c) = c := by
    intro c; rw [Algebra.algebraMap_eq_smul_one, map_smul, h01, smul_eq_mul, mul_one]
  let φ : A →+* k :=
    { toFun := Δ 0, map_one' := h01, map_mul' := hmul0, map_zero' := map_zero _,
      map_add' := map_add _ }
  have hsurj : Function.Surjective φ := fun c => ⟨algebraMap k A c, halg c⟩
  have hQmax : (RingHom.ker φ).IsMaximal := RingHom.ker_isMaximal_of_surjective φ hsurj
  have hmemQ : ∀ u, u ∈ RingHom.ker φ ↔ Δ 0 u = 0 := fun u => RingHom.mem_ker
  set Q := RingHom.ker φ with hQ
  have h11 : Δ 1 (1 : A) = 0 := by
    have := hL 1 hN1 1 1
    simp [Finset.sum_range_succ, h01] at this
    linear_combination this
  have ha : ∀ m, ∀ u ∈ Q ^ m, ∀ l < m, l < N → Δ l u = 0 := by
    intro m
    induction m with
    | zero => intro u _ l hl; omega
    | succ m ih =>
      intro u hu l hlm hlN
      rw [pow_succ] at hu
      refine Submodule.mul_induction_on (C := fun u => Δ l u = 0) hu ?_ ?_
      · intro x hx y hy
        show Δ l (x * y) = 0
        rw [hL l hlN]
        refine Finset.sum_eq_zero fun p hp => ?_
        have hp' : p ≤ l := Nat.lt_succ_iff.mp (Finset.mem_range.mp hp)
        by_cases hpm : p < m
        · rw [ih x hx p hpm (by omega)]; simp
        · have : l - p = 0 := by omega
          rw [this, (hmemQ y).mp hy]; simp
      · intro x y hx hy
        show Δ l (x + y) = 0
        rw [map_add, hx, hy, add_zero]
  set π' : A := π - algebraMap k A (Δ 0 π) with hπ'
  have hπ'Q : π' ∈ Q := by
    rw [hmemQ, hπ', map_sub, halg, sub_self]
  have hπ'1 : Δ 1 π' = 1 := by
    rw [hπ', map_sub, Algebra.algebraMap_eq_smul_one, map_smul, h11, smul_zero, sub_zero, hπ]
  have hb : ∀ m < N, Δ m (π' ^ m) = (m.factorial : k) := by
    intro m
    induction m with
    | zero => intro _; simp [h01]
    | succ m ih =>
      intro hm
      rw [pow_succ', hL (m+1) hm]
      rw [Finset.sum_eq_single 1]
      · simp [hπ'1, ih (by omega), Nat.factorial_succ]
      · intro p hp hp1
        have hp' := Finset.mem_range.mp hp
        rcases Nat.lt_or_gt_of_ne hp1 with h | h
        · have : p = 0 := by omega
          subst this; rw [(hmemQ π').mp hπ'Q]; simp
        · rw [ha m (π' ^ m) (Ideal.pow_mem_pow hπ'Q m) (m + 1 - p) (by omega) (by omega)]; simp
      · intro h; simp at h
  have hQ0 : Q ≠ ⊥ := by
    intro h
    have : π' = 0 := by rw [← Ideal.mem_bot, ← h]; exact hπ'Q
    rw [this, map_zero] at hπ'1; exact zero_ne_one hπ'1
  have hnot : ∀ m < N, π' ^ m ∉ Q ^ (m + 1) := by
    intro m hm hmem
    have := ha (m + 1) _ hmem m (by omega) hm
    rw [hb m hm] at this
    exact (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero m)) this
  have hc : ∀ f : A, (∀ l < N, Δ l f = 0) → ∀ m ≤ N, f ∈ Q ^ m := by
    intro f hf m
    induction m with
    | zero => intro _; simp
    | succ m ih =>
      intro hm
      have hfm := ih (by omega)
      have hI : Ideal.span {π' ^ m} ⊔ Q ^ (m + 1) = Q ^ m := by
        apply Ideal.eq_prime_pow_of_succ_lt_of_le hQ0
        · refine lt_of_le_of_ne le_sup_right ?_
          intro h; apply hnot m (by omega); rw [h]
          exact Ideal.mem_sup_left (Ideal.mem_span_singleton_self _)
        · exact sup_le ((Ideal.span_singleton_le_iff_mem _).mpr (Ideal.pow_mem_pow hπ'Q m))
            (Ideal.pow_le_pow_right (Nat.le_succ m))
      rw [← hI] at hfm
      obtain ⟨y, hy, g, hg, hyg⟩ := Submodule.mem_sup.mp hfm
      obtain ⟨d, rfl⟩ := Ideal.mem_span_singleton'.mp hy
      have hdc : d - algebraMap k A (Δ 0 d) ∈ Q := by
        rw [hmemQ, map_sub, halg, sub_self]
      have hrest : (d - algebraMap k A (Δ 0 d)) * π' ^ m ∈ Q ^ (m + 1) := by
        rw [pow_succ']; exact Ideal.mul_mem_mul hdc (Ideal.pow_mem_pow hπ'Q m)
      have hrg : (d - algebraMap k A (Δ 0 d)) * π' ^ m + g ∈ Q ^ (m + 1) :=
        Ideal.add_mem _ hrest hg
      have e : f = (Δ 0 d) • π' ^ m + ((d - algebraMap k A (Δ 0 d)) * π' ^ m + g) := by
        rw [← hyg, Algebra.smul_def]; ring
      have hΔ : Δ m f = Δ 0 d * m.factorial := by
        rw [e, map_add, map_smul, hb m (by omega), ha (m + 1) _ hrg m (by omega) (by omega),
          smul_eq_mul, add_zero]
      have hc0 : Δ 0 d = 0 := by
        have := hf m (by omega); rw [hΔ] at this
        exact (mul_eq_zero.mp this).resolve_right (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero m))
      rw [e]; exact Ideal.add_mem _ (by rw [hc0, zero_smul]; exact Ideal.zero_mem _) hrg
  exact ⟨Q, hQmax, hmemQ, fun f hf => hc f hf N le_rfl⟩

end GlobalTheory
