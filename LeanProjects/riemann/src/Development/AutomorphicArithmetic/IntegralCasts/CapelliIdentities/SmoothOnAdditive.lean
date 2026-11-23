import Mathlib

noncomputable def UpperTheory.Reformulated.B.SmoothOnAdditive.SmOn.{u_1, u_3} :
    {E : Type u_1} →
      {V : Type u_3} →
        [inst : NormedAddCommGroup E] →
          [NormedSpace ℝ E] → [inst : NormedAddCommGroup V] → [NormedSpace ℝ V] → Set E → (E → V) → Prop :=
    fun {E : Type u_1} {V : Type u_3} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup V] [NormedSpace ℝ V]
        (A : Set E) (f : E → V) ↦
      ∀ a ∈ A, ∃ (U : Set E) (F : E → V), IsOpen U ∧ a ∈ U ∧ ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) F U ∧ ∀ g ∈ U, g ∈ A → f g = F g

namespace UpperTheory.Reformulated.B.SmoothOnAdditive.Helpers

private lemma smOn_zero {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup V] [NormedSpace ℝ V] (A : Set E) :
    UpperTheory.Reformulated.B.SmoothOnAdditive.SmOn A (fun _ : E => (0 : V)) := by
  intro a _
  exact ⟨Set.univ, fun _ => 0, isOpen_univ, Set.mem_univ _, contDiffOn_const, fun _ _ _ => rfl⟩

private lemma smOn_add {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup V] [NormedSpace ℝ V] {A : Set E} {f g : E → V}
    (hf : UpperTheory.Reformulated.B.SmoothOnAdditive.SmOn A f) (hg : UpperTheory.Reformulated.B.SmoothOnAdditive.SmOn A g) :
    UpperTheory.Reformulated.B.SmoothOnAdditive.SmOn A (fun x => f x + g x) := by
  intro a ha
  obtain ⟨U1, F1, hU1, ha1, hF1, he1⟩ := hf a ha
  obtain ⟨U2, F2, hU2, ha2, hF2, he2⟩ := hg a ha
  refine ⟨U1 ∩ U2, fun x => F1 x + F2 x, hU1.inter hU2, ⟨ha1, ha2⟩,
    (hF1.mono Set.inter_subset_left).add (hF2.mono Set.inter_subset_right), ?_⟩
  intro x hx hxA
  simp only [he1 x hx.1 hxA, he2 x hx.2 hxA]

end UpperTheory.Reformulated.B.SmoothOnAdditive.Helpers

open UpperTheory.Reformulated.B.SmoothOnAdditive.Helpers in
theorem UpperTheory.Reformulated.B.SmoothOnAdditive.main.{u_1, u_2, u_3} :
    ∀ {E : Type u_1} {V : Type u_2} {ι : Type u_3} [inst : NormedAddCommGroup E] [inst_1 : NormedSpace ℝ E]
      [inst_2 : NormedAddCommGroup V] [inst_3 : NormedSpace ℝ V] {A : Set E} {f : ι → E → V} (s : Finset ι),
      (∀ i ∈ s, UpperTheory.Reformulated.B.SmoothOnAdditive.SmOn A (f i)) → UpperTheory.Reformulated.B.SmoothOnAdditive.SmOn A fun (a : E) ↦ ∑ i ∈ s, f i a := by
  intro E V ι _ _ _ _ A f s
  classical
  induction s using Finset.induction_on with
  | empty =>
    intro _
    simpa using (smOn_zero (V := V) A)
  | insert j s hj ih =>
    intro h
    have h1 := h j (Finset.mem_insert_self j s)
    have h2 := ih (fun i hi => h i (Finset.mem_insert_of_mem hi))
    have := smOn_add h1 h2
    simpa [Finset.sum_insert hj] using this
