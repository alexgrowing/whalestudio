import Mathlib

open IsLocalRing

theorem UpperTheory.V.CA.g_gram :
    ∀ (K ι : Type) [Field K] [Fintype ι] [DecidableEq ι] (s : Set (Matrix ι ι K)),
      Submodule.span K s = ⊤ ↔ ∃ x : ι × ι → Matrix ι ι K, (∀ a, x a ∈ s) ∧
        Matrix.det (Matrix.of fun a b : ι × ι => (x a * x b).trace) ≠ 0 := by
  intro K ι _ _ _ s
  have hG : ∀ (x : ι × ι → Matrix ι ι K) (v : ι × ι → K) (a : ι × ι),
      (Matrix.of (fun a b : ι × ι => (x a * x b).trace)).mulVec v a
        = (x a * ∑ b, v b • x b).trace := by
    intro x v a
    simp only [Matrix.mulVec, dotProduct, Matrix.of_apply, Finset.mul_sum, Matrix.trace_sum,
      Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul]
    exact Finset.sum_congr rfl fun b _ => mul_comm _ _
  constructor
  · intro hs
    obtain ⟨b, hbs, hspan, hli⟩ := exists_linearIndependent K s
    have htop : ⊤ ≤ Submodule.span K (Set.range (Subtype.val : b → Matrix ι ι K)) := by
      rw [Subtype.range_coe, hspan, hs]
    let B := Module.Basis.mk hli htop
    let e := B.indexEquiv (Matrix.stdBasis K ι ι)
    let x : ι × ι → Matrix ι ι K := fun a => (e.symm a : Matrix ι ι K)
    have hxli : LinearIndependent K x := hli.comp e.symm e.symm.injective
    have hxspan : Submodule.span K (Set.range x) = ⊤ := by
      have hr : Set.range x = Set.range (Subtype.val : b → Matrix ι ι K) := by
        ext m
        constructor
        · rintro ⟨a, rfl⟩
          exact ⟨e.symm a, rfl⟩
        · rintro ⟨c, rfl⟩
          exact ⟨e c, by simp [x]⟩
      rw [hr, Subtype.range_coe, hspan, hs]
    refine ⟨x, fun a => hbs (e.symm a).2, ?_⟩
    intro hdet
    obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
    have hxy : ∀ a, (x a * ∑ b, v b • x b).trace = 0 := fun a => by
      rw [← hG x v a, hv]
      rfl
    have hall : ∀ z ∈ Submodule.span K (Set.range x), (z * ∑ b, v b • x b).trace = 0 := by
      intro z hz
      induction hz using Submodule.span_induction with
      | mem z hz =>
        obtain ⟨a, rfl⟩ := hz
        exact hxy a
      | zero => simp
      | add z w _ _ hz hw => rw [add_mul, Matrix.trace_add, hz, hw, add_zero]
      | smul c z _ hz => rw [Matrix.smul_mul, Matrix.trace_smul, hz, smul_zero]
    have hy0 : ∑ b, v b • x b = 0 := by
      ext i k
      have h := hall (Matrix.single k i 1) (by rw [hxspan]; exact Submodule.mem_top)
      rw [Matrix.trace_single_mul, one_smul] at h
      simpa using h
    apply hv0
    funext a
    exact Fintype.linearIndependent_iff.mp hxli v hy0 a
  · rintro ⟨x, hxs, hdet⟩
    rcases isEmpty_or_nonempty ι with hι | hι
    · exact Subsingleton.elim _ _
    have hli : LinearIndependent K x := by
      rw [Fintype.linearIndependent_iff]
      intro g hg
      have hm : (Matrix.of fun a b : ι × ι => (x a * x b).trace).mulVec g = 0 := by
        funext a
        rw [hG, hg, Matrix.mul_zero, Matrix.trace_zero]
        rfl
      exact fun i => congrFun (Matrix.eq_zero_of_mulVec_eq_zero hdet hm) i
    have htop := hli.span_eq_top_of_card_eq_finrank (by
      rw [Module.finrank_matrix, Module.finrank_self, mul_one, Fintype.card_prod])
    rw [eq_top_iff, ← htop]
    exact Submodule.span_mono (Set.range_subset_iff.mpr hxs)
