import Mathlib

universe u_1 u_2 u_3 u_4

namespace Bl.general_b_fact_right_bis_form

private theorem aux {R : Type u_1} [CommRing R] {ι : Type u_2} [Fintype ι] [DecidableEq ι]
    {M : ι → Type u_3} [(i : ι) → AddCommGroup (M i)] [(i : ι) → Module R (M i)]
    {A : Type u_4} [CommRing A] [Algebra R A]
    (φ : (i : ι) → M i →ₗ[R] A) (S : (i : ι) → Set (M i)) (T : Submodule R A)
    (hS : ∀ s : (i : ι) → M i, (∀ i, s i ∈ S i) → (∏ i, φ i (s i)) ∈ T) (F : Finset ι) :
    ∀ m : (i : ι) → M i, (∀ i ∈ F, m i ∈ Submodule.span R (S i)) → (∀ i ∉ F, m i ∈ S i) →
      (∏ i, φ i (m i)) ∈ T := by
  refine Finset.induction_on F ?_ ?_
  · intro m _ h2
    exact hS m (fun i => h2 i (by simp))
  · intro a F ha ih m h1 h2
    have hlin : ∀ y : M a, (∏ i, φ i (Function.update m a y i)) =
        φ a y * ∏ i ∈ Finset.univ.erase a, φ i (m i) := by
      intro y
      rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ a)]
      congr 1
      · rw [Function.update_self]
      · refine Finset.prod_congr rfl ?_
        intro i hi
        rw [Function.update_of_ne (Finset.ne_of_mem_erase hi)]
    have hsub : Submodule.span R (S a) ≤
        T.comap ((LinearMap.mulRight R (∏ i ∈ Finset.univ.erase a, φ i (m i))).comp (φ a)) := by
      rw [Submodule.span_le]
      intro y hy
      rw [SetLike.mem_coe, Submodule.mem_comap, LinearMap.comp_apply, LinearMap.mulRight_apply,
        ← hlin y]
      refine ih (Function.update m a y) ?_ ?_
      · intro i hi
        have hia : i ≠ a := fun h => ha (h ▸ hi)
        rw [Function.update_of_ne hia]
        exact h1 i (Finset.mem_insert_of_mem hi)
      · intro i hi
        by_cases hia : i = a
        · subst hia
          rw [Function.update_self]
          exact hy
        · rw [Function.update_of_ne hia]
          exact h2 i (by simp [hia, hi])
    have hx := hsub (h1 a (Finset.mem_insert_self a F))
    rw [Submodule.mem_comap, LinearMap.comp_apply, LinearMap.mulRight_apply, ← hlin (m a),
      Function.update_eq_self] at hx
    exact hx

theorem goal1 :
  ∀ {R : Type u_1} [inst : CommRing.{u_1} R] {ι : Type u_2} [inst_1 : Fintype.{u_2} ι] [DecidableEq.{u_2 + 1} ι]
  {M : ι → Type u_3} [inst_3 : (i : ι) → AddCommGroup.{u_3} (M i)] [inst_4 : (i : ι) → Module.{u_1, u_3} R (M i)]
  {A : Type u_4} [inst_5 : CommRing.{u_4} A] [inst_6 : Algebra.{u_1, u_4} R A]
  (φ : (i : ι) → LinearMap.{u_1, u_1, u_3, u_4} (RingHom.id.{u_1} R) (M i) A) (S : (i : ι) → Set.{u_3} (M i))
  (T : Submodule.{u_1, u_4} R A),
  (∀ (s : (i : ι) → M i),
      (∀ (i : ι), Membership.mem.{u_3, u_3} (S i) (s i)) →
        Membership.mem.{u_4, u_4} T
          (Finset.prod.{u_2, u_4} Finset.univ.{u_2} fun (i : ι) ↦
            DFunLike.coe.{max (u_3 + 1) (u_4 + 1), u_3 + 1, u_4 + 1} (φ i) (s i))) →
    ∀ (m : (i : ι) → M i),
      (∀ (i : ι), Membership.mem.{u_3, u_3} (Submodule.span.{u_1, u_3} R (S i)) (m i)) →
        Membership.mem.{u_4, u_4} T
          (Finset.prod.{u_2, u_4} Finset.univ.{u_2} fun (i : ι) ↦
            DFunLike.coe.{max (u_3 + 1) (u_4 + 1), u_3 + 1, u_4 + 1} (φ i) (m i)) := by
  intro R _ ι _ _ M _ _ A _ _ φ S T h m hm
  exact aux φ S T h Finset.univ m (fun i _ => hm i) (fun i hi => absurd (Finset.mem_univ i) hi)

end Bl.general_b_fact_right_bis_form
