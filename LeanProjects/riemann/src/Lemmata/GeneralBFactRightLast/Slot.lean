import Mathlib

universe u_1 u_2 u_3

namespace Bl.general_b_fact_right_last

private lemma intersection_update_fsHerm_neg_one {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] (f : E → F) (c : ℂ)
    (h : ∀ a b, inner ℂ (f a) (f b) = c * inner ℂ a b) (M : Submodule ℂ F)
    (hM : IsClosed (M : Set F)) (B : Set E)
    (hB : (Submodule.span ℂ B).topologicalClosure = ⊤) (hBM : ∀ v ∈ B, f v ∈ M) (v : E) :
    f v ∈ M := by
  have hadd : ∀ a b, f (a + b) = f a + f b := by
    intro a b
    have h0 : inner ℂ (f (a + b) - (f a + f b)) (f (a + b) - (f a + f b)) = 0 := by
      simp only [inner_sub_left, inner_sub_right, inner_add_left, inner_add_right, h]
      ring
    exact sub_eq_zero.mp (inner_self_eq_zero.mp h0)
  have hsmul : ∀ (r : ℂ) a, f (r • a) = r • f a := by
    intro r a
    have h0 : inner ℂ (f (r • a) - r • f a) (f (r • a) - r • f a) = 0 := by
      simp only [inner_sub_left, inner_sub_right, inner_smul_left, inner_smul_right, h]
      ring
    exact sub_eq_zero.mp (inner_self_eq_zero.mp h0)
  let L : E →ₗ[ℂ] F := { toFun := f, map_add' := hadd, map_smul' := fun r a => hsmul r a }
  have hbd : ∀ a, ‖L a‖ ≤ Real.sqrt ‖c‖ * ‖a‖ := by
    intro a
    have h2 : ‖f a‖ ^ 2 ≤ ‖c‖ * ‖a‖ ^ 2 := by
      have e1 : ‖f a‖ ^ 2 = RCLike.re (inner ℂ (f a) (f a)) :=
        (inner_self_eq_norm_sq (𝕜 := ℂ) (f a)).symm
      rw [e1, h a a]
      calc RCLike.re (c * inner ℂ a a) ≤ ‖c * inner ℂ a a‖ := RCLike.re_le_norm _
        _ = ‖c‖ * ‖inner ℂ a a‖ := norm_mul _ _
        _ ≤ ‖c‖ * (‖a‖ * ‖a‖) :=
          mul_le_mul_of_nonneg_left (norm_inner_le_norm a a) (norm_nonneg _)
        _ = ‖c‖ * ‖a‖ ^ 2 := by ring
    have hs := Real.sq_sqrt (norm_nonneg c)
    have hs0 := Real.sqrt_nonneg ‖c‖
    rw [← hs] at h2
    show ‖f a‖ ≤ _
    nlinarith [norm_nonneg (f a), norm_nonneg a, mul_nonneg hs0 (norm_nonneg a)]
  have hcont : Continuous L := AddMonoidHomClass.continuous_of_bound L _ hbd
  have hcl : IsClosed ((M.comap L : Submodule ℂ E) : Set E) := hM.preimage hcont
  have h1 : Submodule.span ℂ B ≤ M.comap L :=
    Submodule.span_le.mpr (fun b hb => Submodule.mem_comap.mpr (hBM b hb))
  have h2 := Submodule.topologicalClosure_minimal _ h1 hcl
  rw [hB] at h2
  exact Submodule.mem_comap.mp (h2 Submodule.mem_top)

theorem goal1 :
  ∀ {ι : Type u_1} [inst : Fintype.{u_1} ι] [DecidableEq.{u_1 + 1} ι] {H : ι → Type u_2}
  [inst_2 : (i : ι) → NormedAddCommGroup.{u_2} (H i)] [inst_3 : (i : ι) → InnerProductSpace.{0, u_2} Complex (H i)]
  {Hs : Type u_3} [inst_4 : NormedAddCommGroup.{u_3} Hs] [inst_5 : InnerProductSpace.{0, u_3} Complex Hs]
  (tens : ((i : ι) → H i) → Hs),
  (∀ (x y : (i : ι) → H i),
      Eq.{1} (Inner.inner.{0, u_3} Complex (tens x) (tens y))
        (Finset.prod.{u_1, 0} Finset.univ.{u_1} fun (i : ι) ↦ Inner.inner.{0, u_2} Complex (x i) (y i))) →
    ∀ (M : Submodule.{0, u_3} Complex Hs),
      IsClosed.{u_3} (SetLike.coe.{u_3, u_3} M) →
        ∀ (A : (i : ι) → Set.{u_2} (H i)),
          (∀ (i : ι),
              Eq.{u_2 + 1} (Submodule.topologicalClosure.{0, u_2} (Submodule.span.{0, u_2} Complex (A i)))
                Top.top.{u_2}) →
            (∀ (x : (i : ι) → H i),
                (∀ (i : ι), Membership.mem.{u_2, u_2} (A i) (x i)) → Membership.mem.{u_3, u_3} M (tens x)) →
              ∀ (x : (i : ι) → H i), Membership.mem.{u_3, u_3} M (tens x) := by
  intro ι _ _ H _ _ Hs _ _ tens htens M hM A hA hAM
  have key : ∀ S : Finset ι, ∀ x : (i : ι) → H i, (∀ i, i ∉ S → x i ∈ A i) → tens x ∈ M := by
    intro S
    induction S using Finset.induction_on with
    | empty => intro x hx; exact hAM x (fun i => hx i (by simp))
    | @insert j S hj ih =>
      intro x hx
      have hj' : ∀ v ∈ A j, tens (Function.update x j v) ∈ M := by
        intro v hv
        apply ih
        intro i hi
        by_cases hij : i = j
        · subst hij; simpa using hv
        · rw [Function.update_of_ne hij]; exact hx i (by simp [hij, hi])
      have hall := intersection_update_fsHerm_neg_one (fun v => tens (Function.update x j v))
        (∏ i ∈ Finset.univ.erase j, inner ℂ (x i) (x i)) ?_ M hM (A j) (hA j) hj' (x j)
      · simpa using hall
      · intro a b
        simp only [htens]
        rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ j)]
        simp only [Function.update_self]
        rw [mul_comm]
        congr 1
        apply Finset.prod_congr rfl
        intro i hi
        rw [Function.update_of_ne (Finset.ne_of_mem_erase hi),
          Function.update_of_ne (Finset.ne_of_mem_erase hi)]
  intro x
  exact key Finset.univ x (fun i hi => absurd (Finset.mem_univ i) hi)

end Bl.general_b_fact_right_last
