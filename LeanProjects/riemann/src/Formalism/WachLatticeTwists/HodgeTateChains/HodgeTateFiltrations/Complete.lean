import Formalism.WachLatticeTwists.HodgeTateChains.Statement

noncomputable section

namespace Formalism.RepresentationBoundsCohomology.TorsionBoundCyclotomic

lemma mem_pow_smul_top {R : Type} [CommRing R] {Xm : Type} [AddCommGroup Xm] [Module R Xm] (ϖ : R)
    (n : ℕ) (x : Xm) :
    x ∈ ((Ideal.span {ϖ}) ^ n • (⊤ : Submodule R Xm)) ↔ ∃ y, x = ϖ ^ n • y := by
  rw [Ideal.span_singleton_pow, Submodule.ideal_span_singleton_smul,
    Submodule.mem_smul_pointwise_iff_exists]
  constructor
  · rintro ⟨b, _, rfl⟩; exact ⟨b, rfl⟩
  · rintro ⟨y, rfl⟩; exact ⟨y, trivial, rfl⟩

lemma haus_of {R : Type} [CommRing R] {Xm : Type} [AddCommGroup Xm] [Module R Xm] (ϖ : R)
    (hc : IsAdicComplete (Ideal.span {ϖ}) Xm) (x : Xm) (h : ∀ n : ℕ, ∃ y, x = ϖ ^ n • y) : x = 0 := by
  apply hc.toIsHausdorff.haus
  intro n
  rw [SModEq.zero, mem_pow_smul_top]
  exact h n

theorem onePlus : StatOnePlus := by
  intro R _ Xm _ _ ϖ hc E
  constructor
  · intro x x' hxx
    have hd : x - x' = -(ϖ • E (x - x')) := by
      have h : x + ϖ • E x = x' + ϖ • E x' := hxx
      rw [map_sub, smul_sub, neg_sub, sub_eq_sub_iff_add_eq_add, h, add_comm]
    apply sub_eq_zero.1
    apply haus_of ϖ hc
    intro n
    induction n with
    | zero => exact ⟨x - x', by simp⟩
    | succ n ih =>
      obtain ⟨y, hy⟩ := ih
      refine ⟨-(E y), ?_⟩
      rw [hd]
      conv_lhs => rw [hy]
      rw [map_smul, smul_smul, ← pow_succ', smul_neg]
  · intro y
    let a : ℕ → Xm := fun n => (fun v => -(E v))^[n] y
    have ha0 : a 0 = y := rfl
    have has : ∀ n, a (n + 1) = -(E (a n)) := fun n => Function.iterate_succ_apply' _ _ _
    let f : ℕ → Xm := fun n => ∑ k ∈ Finset.range n, ϖ ^ k • a k
    have hfs : ∀ n, f (n + 1) = f n + ϖ ^ n • a n := fun n => Finset.sum_range_succ _ _
    have hid : ∀ n, f n + ϖ • E (f n) = y - ϖ ^ n • a n := by
      intro n
      induction n with
      | zero => simp [f, ha0]
      | succ n ih =>
        rw [hfs, map_add, smul_add, has, map_smul, smul_smul, ← pow_succ', smul_neg]
        have : f n + ϖ ^ n • a n + (ϖ • E (f n) + ϖ ^ (n + 1) • E (a n))
            = (f n + ϖ • E (f n)) + ϖ ^ n • a n + ϖ ^ (n + 1) • E (a n) := by abel
        rw [this, ih]; abel
    have hcau : ∀ {m n : ℕ}, m ≤ n →
        f m ≡ f n [SMOD ((Ideal.span {ϖ}) ^ m • (⊤ : Submodule R Xm))] := by
      intro m n hmn
      rw [SModEq.sub_mem, mem_pow_smul_top]
      induction n, hmn using Nat.le_induction with
      | base => exact ⟨0, by simp⟩
      | succ n hmn ih =>
        obtain ⟨t, ht⟩ := ih
        refine ⟨t - ϖ ^ (n - m) • a n, ?_⟩
        rw [hfs, smul_sub, ← ht, smul_smul, ← pow_add, Nat.add_sub_cancel' hmn]
        abel
    obtain ⟨L, hL⟩ := hc.toIsPrecomplete.prec hcau
    refine ⟨L, ?_⟩
    apply sub_eq_zero.1
    apply haus_of ϖ hc
    intro n
    have h1 := hL n
    rw [SModEq.sub_mem, mem_pow_smul_top] at h1
    obtain ⟨t, ht⟩ := h1
    refine ⟨-(t + ϖ • E t) - a n, ?_⟩
    have hLf : L = f n - ϖ ^ n • t := by rw [← ht]; abel
    have h2 : L + ϖ • E L - y = (f n + ϖ • E (f n)) - y - (ϖ ^ n • t + ϖ • E (ϖ ^ n • t)) := by
      rw [hLf, map_sub, smul_sub]; abel
    show L + ϖ • E L - y = _
    rw [h2, hid, map_smul, smul_sub, smul_neg, smul_add, smul_comm ϖ (ϖ ^ n)]
    abel

theorem third_estimate_of_first_two (h1 : StatOnePlus) : PerturbationOperatorIntegral := by
  intro R _ Xm _ _ ϖ z hc hz g S B hgS hSg
  have hb := h1 R Xm ϖ hc (S ∘ₗ B ∘ₗ g)
  have key : ∀ x, (g x + (z * ϖ) • B (g x)) - x
      = g (x + ϖ • S (B (g x))) - (x + ϖ • S (B (g x))) := by
    intro x
    have h := hgS (B (g x))
    rw [map_add, map_smul, mul_comm z ϖ, mul_smul, ← h, smul_sub]; abel
  have hinj : ∀ x, g x = x → x = 0 := fun x hx => hz x (by rw [← hSg, hx, sub_self, map_zero])
  refine ⟨?_, ?_, ?_⟩
  · intro x hx
    have h0 : g (x + ϖ • S (B (g x))) = x + ϖ • S (B (g x)) :=
      sub_eq_zero.1 (by rw [← key, hx, sub_self])
    have h2 := hinj _ h0
    apply hb.1
    show x + ϖ • S (B (g x)) = 0 + ϖ • S (B (g 0))
    rw [h2]; simp
  · intro y
    constructor
    · rintro ⟨x, rfl⟩; exact ⟨_, key x⟩
    · rintro ⟨x, rfl⟩
      obtain ⟨x', hx'⟩ := hb.2 x
      have hx'' : x' + ϖ • S (B (g x')) = x := hx'
      exact ⟨x', by rw [key, hx'']⟩
  · intro x
    obtain ⟨x', hx'⟩ := hb.2 (S x)
    have hx'' : x' + ϖ • S (B (g x')) = S x := hx'
    exact ⟨x', by rw [key, hx'', hgS]⟩

theorem t3 : PerturbationOperatorIntegral := third_estimate_of_first_two onePlus

end Formalism.RepresentationBoundsCohomology.TorsionBoundCyclotomic
