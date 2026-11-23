import Mathlib

open CategoryTheory

theorem UpperTheory.Reformulated.B.DYra4.main.{u} :
    ∀ (S : ℕ → Type u) [∀ (a : ℕ), Finite (S a)] [∀ (a : ℕ), Nonempty (S a)] (t : (a : ℕ) → S (a + (1 : ℕ)) → S a),
      ∃ (s : (a : ℕ) → S a), ∀ (a : ℕ), t a (s (a + (1 : ℕ))) = s a := by
  intro S _ _ t
  let F : ℕᵒᵖ ⥤ Type u := Functor.ofOpSequence (X := S) (fun n => TypeCat.ofHom (t n))
  haveI : ∀ j : ℕᵒᵖ, Finite (F.obj j) := fun j => inferInstanceAs (Finite (S j.unop))
  haveI : ∀ j : ℕᵒᵖ, Nonempty (F.obj j) := fun j => inferInstanceAs (Nonempty (S j.unop))
  obtain ⟨x, hx⟩ := nonempty_sections_of_finite_inverse_system F
  refine ⟨fun a => x (Opposite.op a), fun a => ?_⟩
  have h := hx (homOfLE (Nat.le_succ a)).op
  rw [Functor.ofOpSequence_map_homOfLE_succ] at h
  exact h
