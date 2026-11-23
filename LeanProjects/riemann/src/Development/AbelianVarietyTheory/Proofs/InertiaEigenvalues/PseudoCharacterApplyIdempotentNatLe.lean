import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.DataN
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsPsCharOne

open Formalism.MainNotions.N GlobalTheory.PsChar

namespace GlobalTheory.PsChar

section
variable {M A : Type*} [Monoid M] [CommRing A]

theorem alt_const_idem (T : M → A) (e : M) (he : e * e = e) :
    ∀ n : ℕ, alt T n (fun _ => e) = ∏ i ∈ Finset.range n, (T e - (i : A))
  | 0 => by simp [alt]
  | n + 1 => by
    have h1 : Fin.tail (fun _ : Fin (n + 1) => e) = fun _ : Fin n => e := rfl
    have h2 : ∀ i : Fin n, Function.update (fun _ : Fin n => e) i e = fun _ => e := by
      intro i; exact Function.update_eq_self i (fun _ : Fin n => e)
    rw [alt, h1]
    simp only [he, h2, alt_const_idem T e he n, Finset.prod_range_succ, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    ring

theorem alt_idem_last (T : M → A) (e y : M) (he : e * e = e) (hy : e * y = y) (h0 : T e = 0) :
    ∀ n : ℕ, alt T (n + 1) (fun i => if i.val = n then y else e)
      = (-1) ^ n * (n.factorial : A) * T y
  | 0 => by simp [alt]
  | n + 1 => by
    have h1 : Fin.tail (fun i : Fin (n + 1 + 1) => if i.val = n + 1 then y else e)
        = fun i : Fin (n + 1) => if i.val = n then y else e := by
      funext i; simp [Fin.tail]
    have h2 : ∀ i : Fin (n + 1), Function.update (fun i : Fin (n + 1) => if i.val = n then y else e) i
        (e * (if i.val = n then y else e)) = fun i => if i.val = n then y else e := by
      intro i
      have : e * (if i.val = n then y else e) = (if i.val = n then y else e) := by
        split_ifs <;> assumption
      rw [this]
      exact Function.update_eq_self i (fun i : Fin (n + 1) => if i.val = n then y else e)
    have h3 : (if ((0 : Fin (n + 1 + 1)) : ℕ) = n + 1 then y else e) = e := by simp
    rw [alt, h1, h3, h0]
    simp only [h2, alt_idem_last T e y he hy h0 n, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.factorial_succ]
    push_cast
    ring

end

theorem isPsChar_idempotent : ∀ (k R : Type) [Field k] [CharZero k] [Ring R] [Algebra k R] (d : ℕ) (T : R →ₗ[k] k), IsPsChar d (fun x => T x) → ∀ e : R, IsIdempotentElem e → (∃ m : ℕ, m ≤ d ∧ T e = m) ∧ (T e = 0 → ∀ y : R, T (e * y) = 0) := by
  intro k R _ _ _ _ d T hT e he
  have he' : e * e = e := he
  refine ⟨?_, fun h0 y => ?_⟩
  · have h := hT.alt_eq_zero (fun _ => e)
    rw [alt_const_idem _ e he', Finset.prod_eq_zero_iff] at h
    obtain ⟨m, hm, h⟩ := h
    exact ⟨m, Nat.lt_succ_iff.mp (Finset.mem_range.mp hm), sub_eq_zero.mp h⟩
  · have h := hT.alt_eq_zero (fun i => if i.val = d then e * y else e)
    rw [alt_idem_last (fun x => T x) e (e * y) he' (by rw [← mul_assoc, he']) h0 d] at h
    have h1 : ((-1 : k) ^ d * (d.factorial : k)) ≠ 0 :=
      mul_ne_zero (pow_ne_zero _ (by norm_num)) (Nat.cast_ne_zero.mpr d.factorial_ne_zero)
    exact (mul_eq_zero.mp h).resolve_left h1

end GlobalTheory.PsChar
