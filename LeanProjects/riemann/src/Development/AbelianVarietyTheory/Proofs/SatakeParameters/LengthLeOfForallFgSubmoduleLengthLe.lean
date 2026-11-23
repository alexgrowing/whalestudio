import Mathlib
open Pointwise

namespace GlobalTheory

theorem length_le_of_forall_fg_length_le (O M : Type) [CommRing O] [AddCommGroup M] [Module O M] (b : ℕ∞)
    (h : ∀ N : Submodule O M, N.FG → Module.length O N ≤ b) : Module.length O M ≤ b := by
  rw [Module.length_eq_height]
  refine Order.height_le_iff'.2 fun p _ => ?_
  have hx : ∀ i : Fin p.length, ∃ x ∈ p i.succ, x ∉ p i.castSucc :=
    fun i => SetLike.exists_of_lt (p.step i)
  choose x hx1 hx2 using hx
  set N : Submodule O M := Submodule.span O (Set.range x) with hN
  have hNfg : N.FG := Submodule.fg_span (Set.finite_range x)
  have hxN : ∀ i, x i ∈ N := fun i => Submodule.subset_span ⟨i, rfl⟩
  let q : LTSeries (Submodule O N) :=
    { length := p.length
      toFun := fun i => (p i).comap N.subtype
      step := fun i => by
        refine lt_of_le_of_ne (Submodule.comap_mono (p.step i).le) ?_
        intro heq
        have h1 : (⟨x i, hxN i⟩ : N) ∈ (p i.succ).comap N.subtype := hx1 i
        rw [← heq] at h1
        exact hx2 i h1 }
  have h2 : (q.length : ℕ∞) ≤ Order.height (⊤ : Submodule O N) :=
    Order.length_le_height le_top
  calc (p.length : ℕ∞) = q.length := rfl
    _ ≤ Order.height (⊤ : Submodule O N) := h2
    _ = Module.length O N := (Module.length_eq_height (R := O) (M := N)).symm
    _ ≤ b := h N hNfg

end GlobalTheory
