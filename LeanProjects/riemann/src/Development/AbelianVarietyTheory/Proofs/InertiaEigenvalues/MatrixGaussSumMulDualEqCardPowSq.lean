import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MatrixGaussSumSingularAndInvertible
open Matrix Finset
open scoped TensorProduct Classical

namespace GlobalTheory

theorem sum_addChar_trace_mul_eq {k : Type} [Field k] [Fintype k] [DecidableEq k] {R : Type}
    [CommRing R] [IsDomain R] (ψ : AddChar k R) (hψ : ψ.IsPrimitive) {r : ℕ}
    (m : Matrix (Fin r) (Fin r) k) :
    ∑ a : Matrix (Fin r) (Fin r) k, ψ (trace (a * m)) =
      if m = 0 then (Fintype.card k : R) ^ (r ^ 2) else 0 := by
  split_ifs with hm
  · subst hm
    simp only [Matrix.mul_zero, trace_zero, AddChar.map_zero_eq_one, sum_const, card_univ,
      nsmul_eq_mul, mul_one]
    rw [show Fintype.card (Matrix (Fin r) (Fin r) k) = Fintype.card (Fin r → Fin r → k) from rfl]
    simp [Fintype.card_fun, ← pow_mul, sq]
  · obtain ⟨i, j, hij⟩ : ∃ i j, m i j ≠ 0 := by
      by_contra h; push_neg at h; exact hm (Matrix.ext h)
    have h1 := hψ hij
    obtain ⟨c, hc⟩ : ∃ c, ψ (m i j * c) ≠ 1 := by
      by_contra h; push_neg at h; apply h1; ext c; simp [AddChar.mulShift_apply, h]
    set a₀ : Matrix (Fin r) (Fin r) k := Matrix.single j i c
    have ha₀ : trace (a₀ * m) = m i j * c := by
      simp [a₀, Matrix.trace_single_mul, mul_comm]
    set S := ∑ a : Matrix (Fin r) (Fin r) k, ψ (trace (a * m))
    have hS : S = ψ (trace (a₀ * m)) * S := by
      rw [Finset.mul_sum]
      refine Fintype.sum_equiv (Equiv.subRight a₀) _ _ (fun a => ?_)
      simp only [Equiv.subRight_apply, ← AddChar.map_add_eq_mul, Matrix.sub_mul, trace_sub]
      congr 1; ring
    rw [ha₀] at hS
    have : (1 - ψ (m i j * c)) * S = 0 := by rw [sub_mul, one_mul, ← hS, sub_self]
    rcases mul_eq_zero.mp this with h | h
    · exact absurd (sub_eq_zero.mp h).symm hc
    · exact h

end GlobalTheory

namespace GlobalTheory

theorem matrixGaussSum_mul_dual_eq_card_pow : ∀ (k : Type) [Field k] [Fintype k] [DecidableEq k] (R : Type) [CommRing R] [IsDomain R] (ψ : AddChar k R) (ξ : kˣ →* Rˣ) (r : ℕ), ψ.IsPrimitive → ξ ≠ 1 → (∑ x : GL (Fin r) k, (((ξ (Matrix.GeneralLinearGroup.det x))⁻¹ : Rˣ) : R) * ψ (Matrix.trace (1 * (x : Matrix (Fin r) (Fin r) k)))) * (∑ x : GL (Fin r) k, (((ξ⁻¹ (Matrix.GeneralLinearGroup.det x))⁻¹ : Rˣ) : R) * ψ⁻¹ (Matrix.trace (1 * (x : Matrix (Fin r) (Fin r) k)))) = (Fintype.card k : R) ^ (r ^ 2) := by
  intro k _ _ _ R _ _ ψ ξ r hψ hξ
  obtain ⟨hsing, hinv⟩ := GlobalTheory.matrixGaussSum_singular_and_invertible k R ψ ξ r hψ hξ
  let S : Matrix (Fin r) (Fin r) k → R := fun a => ∑ x : GL (Fin r) k,
    (((ξ (Matrix.GeneralLinearGroup.det x))⁻¹ : Rˣ) : R) * ψ (trace (a * (x : Matrix (Fin r) (Fin r) k)))

  have key1 : ∑ a, S a * ψ (-trace a) = (Fintype.card k : R) ^ (r ^ 2) := by
    simp only [S, Finset.sum_mul]
    rw [Finset.sum_comm]
    have hx : ∀ x : GL (Fin r) k, ∑ a : Matrix (Fin r) (Fin r) k,
        (((ξ (Matrix.GeneralLinearGroup.det x))⁻¹ : Rˣ) : R) * ψ (trace (a * (x : Matrix (Fin r) (Fin r) k))) * ψ (-trace a)
        = (((ξ (Matrix.GeneralLinearGroup.det x))⁻¹ : Rˣ) : R) *
          ∑ a : Matrix (Fin r) (Fin r) k, ψ (trace (a * ((x : Matrix (Fin r) (Fin r) k) - 1))) := by
      intro x
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [mul_assoc, ← AddChar.map_add_eq_mul, Matrix.mul_sub, Matrix.mul_one, trace_sub, sub_eq_add_neg]
    simp_rw [hx, sum_addChar_trace_mul_eq ψ hψ]
    rw [Finset.sum_eq_single 1]
    · simp
    · intro x _ hx1
      rw [if_neg, mul_zero]
      intro h
      apply hx1
      ext1
      simpa using sub_eq_zero.mp h
    · simp

  have key2 : ∑ a, S a * ψ (-trace a) =
      ∑ g : GL (Fin r) k, S (g : Matrix (Fin r) (Fin r) k) * ψ (-trace (g : Matrix (Fin r) (Fin r) k)) := by
    symm
    refine Fintype.sum_of_injective (fun g : GL (Fin r) k => (g : Matrix (Fin r) (Fin r) k)) (fun g h e => Units.ext e) _ _ ?_ (fun g => rfl)
    intro a ha
    have hdet : a.det = 0 := by
      by_contra h
      exact ha ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero a h, rfl⟩
    simp only [S]
    rw [hsing a hdet, zero_mul]
  rw [← key1, key2]
  simp only [S]
  simp_rw [hinv]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun g _ => ?_
  simp [MonoidHom.inv_apply, AddChar.inv_apply]
  ring

end GlobalTheory
