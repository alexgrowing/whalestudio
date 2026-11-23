import Mathlib

namespace GlobalTheory

theorem groupAlgebra_single_one_mem_of_span {A X : Type} [CommRing A] [AddCommGroup X]
    (R : Subring (AddMonoidAlgebra A X)) (h0 : ∀ a : A, AddMonoidAlgebra.single 0 a ∈ R) (α : X)
    (h : Ideal.span {a : A | AddMonoidAlgebra.single α a ∈ R} = ⊤) :
    AddMonoidAlgebra.single α (1 : A) ∈ R := by
  have key : ∀ a ∈ Ideal.span {a : A | AddMonoidAlgebra.single α a ∈ R},
      AddMonoidAlgebra.single α a ∈ R := by
    intro a ha
    induction ha using Submodule.span_induction with
    | mem x hx => exact hx
    | zero => rw [AddMonoidAlgebra.single_zero]; exact R.zero_mem
    | add x y _ _ hx hy => rw [AddMonoidAlgebra.single_add]; exact R.add_mem hx hy
    | smul c x _ hx =>
      have := R.mul_mem (h0 c) hx
      rwa [AddMonoidAlgebra.single_mul_single, zero_add] at this
  exact key 1 (h ▸ Submodule.mem_top)

theorem groupAlgebra_subring_eq_top :
    (∀ (A X : Type) [CommRing A] [AddCommGroup X] (I : Type) (e : Module.Basis I ℤ X) (R : Subring (AddMonoidAlgebra A X)), (∀ a : A, AddMonoidAlgebra.single 0 a ∈ R) → (∀ i, Ideal.span {a : A | AddMonoidAlgebra.single (e i) a ∈ R} = ⊤ ∧ Ideal.span {a : A | AddMonoidAlgebra.single (-e i) a ∈ R} = ⊤) → R = ⊤) := by
  intro A X _ _ I e R h0 h
  have hadd : ∀ x y : X, AddMonoidAlgebra.single x (1 : A) ∈ R →
      AddMonoidAlgebra.single y (1 : A) ∈ R → AddMonoidAlgebra.single (x + y) (1 : A) ∈ R := by
    intro x y hx hy
    have := R.mul_mem hx hy
    rwa [AddMonoidAlgebra.single_mul_single, one_mul] at this
  let S : AddSubgroup X :=
    { carrier := {x | AddMonoidAlgebra.single x (1 : A) ∈ R ∧
        AddMonoidAlgebra.single (-x) (1 : A) ∈ R}
      zero_mem' := ⟨h0 1, by rw [neg_zero]; exact h0 1⟩
      add_mem' := fun {x y} hx hy => ⟨hadd _ _ hx.1 hy.1, by
        rw [neg_add]; exact hadd _ _ hx.2 hy.2⟩
      neg_mem' := fun {x} hx => ⟨hx.2, by rw [neg_neg]; exact hx.1⟩ }
  have hall : ∀ x : X, x ∈ S := by
    intro x
    have hx : x ∈ Submodule.span ℤ (Set.range e) := by rw [e.span_eq]; exact Submodule.mem_top
    induction hx using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨i, rfl⟩ := hy
      exact ⟨groupAlgebra_single_one_mem_of_span R h0 _ (h i).1,
        groupAlgebra_single_one_mem_of_span R h0 _ (h i).2⟩
    | zero => exact S.zero_mem
    | add x y _ _ hx hy => exact S.add_mem hx hy
    | smul c x _ hx => exact S.zsmul_mem hx c
  have hs : ∀ (x : X) (a : A), AddMonoidAlgebra.single x a ∈ R := by
    intro x a
    have := R.mul_mem (h0 a) (hall x).1
    rwa [AddMonoidAlgebra.single_mul_single, zero_add, mul_one] at this
  rw [eq_top_iff]
  intro f hf
  clear hf
  induction f using AddMonoidAlgebra.induction_linear with
  | zero => exact R.zero_mem
  | add f g hf hg => exact R.add_mem hf hg
  | single x a => exact hs x a

end GlobalTheory
