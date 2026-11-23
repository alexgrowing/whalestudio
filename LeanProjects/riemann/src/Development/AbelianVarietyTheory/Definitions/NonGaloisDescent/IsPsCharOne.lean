import Mathlib

namespace GlobalTheory.PsChar

variable {M A : Type*} [Monoid M] [CommRing A]

noncomputable def alt (T : M → A) : (n : ℕ) → (Fin n → M) → A
  | 0, _ => 1
  | n + 1, x => T (x 0) * alt T n (Fin.tail x) - ∑ i : Fin n, alt T n (Function.update (Fin.tail x) i (x 0 * Fin.tail x i))

structure IsPsChar (d : ℕ) (T : M → A) : Prop where
  one : T 1 = d
  comm : ∀ x y, T (x * y) = T (y * x)
  alt_eq_zero : ∀ x : Fin (d + 1) → M, alt T (d + 1) x = 0

theorem map_alt {B : Type*} [CommRing B] (f : A →+* B) (T : M → A) :
    ∀ (n : ℕ) (x : Fin n → M), f (alt T n x) = alt (fun g => f (T g)) n x
  | 0, _ => by simp [alt]
  | n + 1, x => by simp [alt, map_alt f T n]

end GlobalTheory.PsChar
