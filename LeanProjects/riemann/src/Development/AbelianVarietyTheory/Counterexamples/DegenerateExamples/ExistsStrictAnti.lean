import Mathlib
import Formalism.JacquetSubsetSums.JacquetSubsetSum

namespace GlobalTheory.ConeCharCheck

def antiMon (r : ℕ) : Submonoid (Multiplicative (Fin r → ℤ)) where
  carrier := {g | Antitone (Multiplicative.toAdd g)}
  one_mem' := fun _ _ _ => le_rfl
  mul_mem' := fun {a b} ha hb i j h => add_le_add (ha h) (hb h)

theorem exists_strictAnti (r : ℕ) : ∃ a : Fin r → ℤ, StrictAnti a :=
  ⟨fun i => -(i : ℤ), fun i j hij => by
    have : (i : ℕ) < j := hij
    simp only; omega⟩

end GlobalTheory.ConeCharCheck
