import Mathlib

namespace GlobalTheory.MultilinearSpanImage

theorem multilinear_mem_span_image_partial {ι : Type} [Fintype ι] [DecidableEq ι] {M : ι → Type}
    [(i : ι) → AddCommGroup (M i)] [(i : ι) → Module ℂ (M i)] {N : Type} [AddCommGroup N]
    [Module ℂ N] (Φ : MultilinearMap ℂ M N) (s : (i : ι) → Set (M i)) (t : Finset ι) :
    ∀ f : (i : ι) → M i, (∀ i ∈ t, f i ∈ Submodule.span ℂ (s i)) → (∀ i, i ∉ t → f i ∈ s i) →
      Φ f ∈ Submodule.span ℂ {y : N | ∃ g : (i : ι) → M i, (∀ i, g i ∈ s i) ∧ y = Φ g} := by
  refine Finset.induction_on t ?_ ?_
  · intro f _ h
    exact Submodule.subset_span ⟨f, fun i => h i (by simp), rfl⟩
  · intro a t ha ih f h1 h2
    have key : ∀ x ∈ Submodule.span ℂ (s a), Φ (Function.update f a x) ∈
        Submodule.span ℂ {y : N | ∃ g : (i : ι) → M i, (∀ i, g i ∈ s i) ∧ y = Φ g} := by
      intro x hx
      induction hx using Submodule.span_induction with
      | mem x hx =>
        apply ih
        · intro i hi
          have hne : i ≠ a := by rintro rfl; exact ha hi
          simpa [hne] using h1 i (Finset.mem_insert_of_mem hi)
        · intro i hi
          by_cases h : i = a
          · subst h; simpa using hx
          · simpa [h] using h2 i (by simp [h, hi])
      | zero => rw [Φ.map_update_zero]; exact Submodule.zero_mem _
      | add x y _ _ hx hy => rw [Φ.map_update_add]; exact Submodule.add_mem _ hx hy
      | smul c x _ hx => rw [Φ.map_update_smul]; exact Submodule.smul_mem _ c hx
    have := key (f a) (h1 a (Finset.mem_insert_self a t))
    simpa using this

theorem multilinear_apply_mem_span_image {ι : Type} [Fintype ι] [DecidableEq ι] {M : ι → Type}
    [inst : (i : ι) → AddCommGroup (M i)] [inst_1 : (i : ι) → Module ℂ (M i)] {N : Type}
    [inst_2 : AddCommGroup N] [inst_3 : Module ℂ N] (Φ : MultilinearMap ℂ M N)
    (s : (i : ι) → Set (M i)) (f : (i : ι) → M i) (hf : ∀ (i : ι), f i ∈ Submodule.span ℂ (s i)) :
    (Φ : ((i : ι) → M i) → N) f ∈ Submodule.span ℂ
      {y : N | ∃ (g : (i : ι) → M i), (∀ (i : ι), g i ∈ s i) ∧ y = (Φ : ((i : ι) → M i) → N) g} :=
  multilinear_mem_span_image_partial Φ s Finset.univ f (fun i _ => hf i) (fun i hi => absurd (Finset.mem_univ i) hi)

end GlobalTheory.MultilinearSpanImage
