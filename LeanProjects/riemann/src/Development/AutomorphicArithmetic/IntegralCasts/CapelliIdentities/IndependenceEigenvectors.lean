import Mathlib

theorem UpperTheory.Reformulated.B.IndependenceEigenvectors.indep :
    ∀ {V I J : Type} [inst : AddCommGroup V]
    [inst_1 : _root_.Module ℂ V] (T : I → Module.End ℂ V) (v : J → V) (lam : J → I → ℂ),
    (∀ (j : J), v j ≠ (0 : V)) →
      (∀ (j : J) (i : I), (T i : V → V) (v j) = lam j i • v j) → Function.Injective lam → LinearIndependent ℂ v := by
  intro V I J _ _ T v lam hv hT hinj
  classical
  rw [linearIndependent_iff']
  intro s
  induction s using Finset.induction_on with
  | empty => intro g _ j hj; simp at hj
  | insert a s ha ih =>
    intro g hg
    rw [Finset.sum_insert ha] at hg
    have hs : ∀ j ∈ s, g j = 0 := by
      intro j hj
      have hne : lam j ≠ lam a := fun h => ha (hinj h ▸ hj)
      obtain ⟨i, hi⟩ := Function.ne_iff.mp hne
      have h1 : (g a * lam a i) • v a + ∑ k ∈ s, (g k * lam k i) • v k = 0 := by
        have h := congrArg (T i) hg
        simpa only [map_add, map_sum, map_smul, map_zero, hT, smul_smul] using h
      have h2 : (g a * lam a i) • v a + ∑ k ∈ s, (g k * lam a i) • v k = 0 := by
        have h := congrArg (fun x => lam a i • x) hg
        simpa only [smul_add, Finset.smul_sum, smul_zero, smul_smul, mul_comm (lam a i)] using h
      have h3 : ∑ k ∈ s, (g k * (lam k i - lam a i)) • v k = 0 := by
        simp only [mul_sub, sub_smul, Finset.sum_sub_distrib]
        exact sub_eq_zero.mpr (add_left_cancel (h1.trans h2.symm))
      have h4 := ih (fun k => g k * (lam k i - lam a i)) h3 j hj
      exact (mul_eq_zero.mp h4).resolve_right (sub_ne_zero.mpr hi)
    have hz : ∑ k ∈ s, g k • v k = 0 :=
      Finset.sum_eq_zero fun k hk => by rw [hs k hk, zero_smul]
    rw [hz, add_zero] at hg
    intro j hj
    rcases Finset.mem_insert.mp hj with rfl | hj
    · exact (smul_eq_zero.mp hg).resolve_right (hv _)
    · exact hs j hj
