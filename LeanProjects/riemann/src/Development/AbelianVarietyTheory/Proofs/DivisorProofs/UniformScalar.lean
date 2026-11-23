import Mathlib

namespace GlobalTheory.UniformScalarBound

theorem uniform_scalar {R V : Type} [CommRing R] [IsDomain R] [AddCommGroup V] [Module R V]
    (A B : Submodule R V) (hA : A.FG) (h : ∀ x ∈ A, ∃ s : R, s ≠ 0 ∧ s • x ∈ B) :
    ∃ s : R, s ≠ 0 ∧ ∀ x ∈ A, s • x ∈ B := by
  classical
  obtain ⟨S, rfl⟩ := hA
  choose! f hf0 hfB using fun x (hx : x ∈ S) => h x (Submodule.subset_span hx)
  refine ⟨∏ g ∈ S, f g, Finset.prod_ne_zero_iff.mpr (fun g hg => hf0 g hg), ?_⟩
  intro x hx
  induction hx using Submodule.span_induction with
  | mem y hy =>
    rw [← Finset.mul_prod_erase S f hy, mul_comm, mul_smul]
    exact B.smul_mem _ (hfB y hy)
  | zero => simp
  | add x y _ _ hx hy => rw [smul_add]; exact B.add_mem hx hy
  | smul a x _ hx => rw [smul_comm]; exact B.smul_mem a hx

theorem main : ∀ {R V : Type} [inst : CommRing R] [IsDomain R] [inst_2 : AddCommGroup V]
    [inst_3 : Module R V] (A B : Submodule R V), Submodule.FG A →
    (∀ x ∈ A, ∃ (s : R), s ≠ (0 : R) ∧ s • x ∈ B) →
    ∃ (s : R), s ≠ (0 : R) ∧ ∀ x ∈ A, s • x ∈ B :=
  fun A B hA h => uniform_scalar A B hA h

end GlobalTheory.UniformScalarBound
