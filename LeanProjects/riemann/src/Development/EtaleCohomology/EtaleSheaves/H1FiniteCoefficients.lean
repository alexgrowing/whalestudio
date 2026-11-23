import Development.EtaleCohomology.EtaleSheaves.NoetherianLocalChartOverlapFiniteComplement

noncomputable section
open LateralTheory.E.StandardEtaleChartsIdempotentGluing

namespace LateralTheory.E.NoetherianChartOverlapFiniteComplement

variable {A K : Type} [CommRing A] [Field K] [Algebra A K]

theorem exists_pow_mul_mem (S : Subalgebra A K) (u : K) (hu : u ≠ 0) (hv : u⁻¹ ∈ S) {x : K}
    (hx : x ∈ Algebra.adjoin A ((S : Set K) ∪ {u})) : ∃ n : ℕ, u⁻¹ ^ n * x ∈ S := by
  induction hx using Algebra.adjoin_induction with
  | mem x hx =>
    rcases hx with hx | hx
    · exact ⟨0, by simpa using hx⟩
    · rw [Set.mem_singleton_iff] at hx; subst hx
      exact ⟨1, by rw [pow_one, inv_mul_cancel₀ hu]; exact S.one_mem⟩
  | algebraMap r => exact ⟨0, by simpa using S.algebraMap_mem r⟩
  | add x y _ _ ihx ihy =>
    obtain ⟨n, hn⟩ := ihx
    obtain ⟨m, hm⟩ := ihy
    refine ⟨n + m, ?_⟩
    have : u⁻¹ ^ (n + m) * (x + y) = u⁻¹ ^ m * (u⁻¹ ^ n * x) + u⁻¹ ^ n * (u⁻¹ ^ m * y) := by ring
    rw [this]
    exact S.add_mem (S.mul_mem (S.pow_mem hv _) hn) (S.mul_mem (S.pow_mem hv _) hm)
  | mul x y _ _ ihx ihy =>
    obtain ⟨n, hn⟩ := ihx
    obtain ⟨m, hm⟩ := ihy
    refine ⟨n + m, ?_⟩
    have : u⁻¹ ^ (n + m) * (x * y) = (u⁻¹ ^ n * x) * (u⁻¹ ^ m * y) := by ring
    rw [this]; exact S.mul_mem hn hm

theorem pow_inv_mul_pow (t : K) (ht : t ≠ 0) (n j : ℕ) :
    (n ≤ j ∧ t⁻¹ ^ n * t ^ j = t ^ (j - n)) ∨ (j < n ∧ t⁻¹ ^ n * t ^ j = t⁻¹ ^ (n - j)) := by
  rcases le_or_gt n j with h | h
  · left
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
    refine ⟨h, ?_⟩
    rw [Nat.add_sub_cancel_left, pow_add, ← mul_assoc, ← mul_pow, inv_mul_cancel₀ ht, one_pow, one_mul]
  · right
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h.le
    refine ⟨h, ?_⟩
    rw [Nat.add_sub_cancel_left, pow_add, mul_comm (t⁻¹ ^ j), mul_assoc, ← mul_pow, inv_mul_cancel₀ ht,
      one_pow, mul_one]

theorem noetherian_local_chart_overlap_finite_complement : LateralTheory.E.LZIdemSumNoetherian.NoetherianLocalChartOverlapFiniteComplement := by
  intro A _ _ _ K _ _ B C t hc hB _
  obtain ⟨S, hS⟩ := hB
  set R := Algebra.adjoin A ({t} : Set K)
  have hfg : (Algebra.adjoin R (S : Set K)).toSubmodule.FG :=
    fg_adjoin_of_finite S.finite_toSet (fun x hx => hc.intB x (hS ▸ Algebra.subset_adjoin hx))
  obtain ⟨G, hG⟩ := hfg
  have hRB : ∀ r : R, (r : K) ∈ B := by
    intro r
    have : R ≤ B := Algebra.adjoin_le (by simpa using hc.tB)
    exact this r.2
  have hAB : ∀ y ∈ Algebra.adjoin R (S : Set K), y ∈ B := by
    intro y hy
    induction hy using Algebra.adjoin_induction with
    | mem x hx => exact hS ▸ Algebra.subset_adjoin hx
    | algebraMap r => exact hRB r
    | add x y _ _ hx hy => exact B.add_mem hx hy
    | mul x y _ _ hx hy => exact B.mul_mem hx hy
  have hGB : ∀ g ∈ G, g ∈ B := by
    intro g hg
    have : g ∈ (Algebra.adjoin R (S : Set K)).toSubmodule := hG ▸ Submodule.subset_span hg
    exact hAB g this
  have hBR : ∀ x ∈ B, x ∈ Submodule.span R (G : Set K) := by
    intro x hx
    rw [hG]
    rw [← hS] at hx
    show x ∈ Algebra.adjoin R (S : Set K)
    induction hx using Algebra.adjoin_induction with
    | mem y hy => exact Algebra.subset_adjoin hy
    | algebraMap a => exact ((Algebra.adjoin R (S : Set K)).restrictScalars A).algebraMap_mem a
    | add x y _ _ hx hy => exact Subalgebra.add_mem _ hx hy
    | mul x y _ _ hx hy => exact Subalgebra.mul_mem _ hx hy
  have hLex : ∀ g ∈ G, ∃ n : ℕ, t⁻¹ ^ n * g ∈ C := by
    intro g hg
    have : g ∈ Algebra.adjoin A ((C : Set K) ∪ {t}) := by
      rw [← hc.glue]; exact Algebra.subset_adjoin (Or.inl (hGB g hg))
    exact exists_pow_mul_mem C t hc.ne hc.tC this
  classical
  let Lf : K → ℕ := fun g => if h : ∃ n : ℕ, t⁻¹ ^ n * g ∈ C then Classical.choose h else 0
  let L := G.sup Lf
  have hL : ∀ g ∈ G, t⁻¹ ^ L * g ∈ C := by
    intro g hg
    have h := hLex g hg
    have hle : Lf g ≤ L := Finset.le_sup hg
    have hspec : t⁻¹ ^ Lf g * g ∈ C := by
      simp only [Lf, dif_pos h]; exact Classical.choose_spec h
    obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hle
    rw [hk, pow_add, mul_comm (t⁻¹ ^ Lf g), mul_assoc]
    exact C.mul_mem (C.pow_mem hc.tC _) hspec
  let N : Submodule A K := Submodule.span A ↑((G ×ˢ Finset.range L).image (fun p => t⁻¹ ^ p.2 * p.1))
  refine ⟨N, ⟨_, rfl⟩, ?_⟩
  set T := Subalgebra.toSubmodule B ⊔ Subalgebra.toSubmodule C ⊔ N with hT
  have hCT : ∀ x ∈ C, x ∈ T := fun x hx => Submodule.mem_sup_left (Submodule.mem_sup_right hx)
  have hBT : ∀ x ∈ B, x ∈ T := fun x hx => Submodule.mem_sup_left (Submodule.mem_sup_left hx)
  have core : ∀ g ∈ G, ∀ m : ℕ, t⁻¹ ^ m * g ∈ T := by
    intro g hg m
    rcases lt_or_ge m L with h | h
    · refine Submodule.mem_sup_right (Submodule.subset_span ?_)
      exact Finset.mem_coe.mpr (Finset.mem_image.mpr ⟨(g, m), Finset.mem_product.mpr ⟨hg, Finset.mem_range.mpr h⟩, rfl⟩)
    · obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le h
      rw [hk, pow_add, mul_comm (t⁻¹ ^ L), mul_assoc]
      exact hCT _ (C.mul_mem (C.pow_mem hc.tC _) (hL g hg))
  have core2 : ∀ g ∈ G, ∀ n j : ℕ, t⁻¹ ^ n * t ^ j * g ∈ T := by
    intro g hg n j
    rcases pow_inv_mul_pow t hc.ne n j with ⟨_, h⟩ | ⟨_, h⟩
    · rw [h]; exact hBT _ (B.mul_mem (B.pow_mem hc.tB _) (hGB g hg))
    · rw [h]; exact core g hg _
  have hspan : ∀ x ∈ Submodule.span R (G : Set K), ∀ n j : ℕ, t⁻¹ ^ n * t ^ j * x ∈ T := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem g hg => exact core2 g hg
    | zero => intro n j; simp
    | add x y _ _ hx hy => intro n j; rw [mul_add]; exact T.add_mem (hx n j) (hy n j)
    | smul r x _ hx =>
      intro n j
      have hr : (r : K) ∈ (Polynomial.aeval (R := A) t).range := by
        rw [← Algebra.adjoin_singleton_eq_range_aeval A t]; exact r.2
      obtain ⟨p, hp⟩ := hr
      have hp' : Polynomial.aeval t p = (r : K) := hp
      have this : r • x = (r : K) * x := rfl
      rw [this, ← hp']
      clear hp hp' this
      induction p using Polynomial.induction_on' with
      | add p q hp' hq' =>
        rw [map_add, add_mul, mul_add]
        exact T.add_mem hp' hq'
      | monomial i a =>
        rw [Polynomial.aeval_monomial]
        have : t⁻¹ ^ n * t ^ j * (algebraMap A K a * t ^ i * x) = a • (t⁻¹ ^ n * t ^ (j + i) * x) := by
          rw [Algebra.smul_def, pow_add]; ring
        rw [this]; exact T.smul_mem a (hx n (j + i))
  intro x hx
  have hx' : x ∈ Algebra.adjoin A ((B : Set K) ∪ {t⁻¹}) := hx
  obtain ⟨n, hn⟩ := exists_pow_mul_mem B t⁻¹ (inv_ne_zero hc.ne) (by rw [inv_inv]; exact hc.tB) hx'
  rw [inv_inv] at hn
  have := hspan _ (hBR _ hn) n 0
  have e : t⁻¹ ^ n * t ^ 0 * (t ^ n * x) = x := by
    rw [pow_zero, mul_one, ← mul_assoc, ← mul_pow, inv_mul_cancel₀ hc.ne, one_pow, one_mul]
  rwa [e] at this

end LateralTheory.E.NoetherianChartOverlapFiniteComplement
