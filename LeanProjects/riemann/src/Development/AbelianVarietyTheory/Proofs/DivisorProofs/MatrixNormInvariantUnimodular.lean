import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTriSelf

set_option autoImplicit false

noncomputable section

open GlobalTheory.TriFrame

namespace GlobalTheory.TriFrame

theorem integral_comb_mul {C : Type} [NormedField C] [IsUltrametricDist C] {r : ℕ}
    (Q N : Matrix (Fin r) (Fin r) C) (hQ : ∀ l k, ‖Q l k‖ ≤ 1) (cf : Fin r → C)
    (h : ∀ l, ‖∑ j, cf j * N l j‖ ≤ 1) : ∀ l, ‖∑ j, cf j * (Q * N) l j‖ ≤ 1 := by
  intro l
  have e : ∑ j, cf j * (Q * N) l j = ∑ k, Q l k * ∑ j, cf j * N k j := by
    simp only [Matrix.mul_apply, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  rw [e]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun k _ => ?_
  rw [norm_mul]
  calc ‖Q l k‖ * ‖∑ j, cf j * N k j‖ ≤ 1 * 1 :=
        mul_le_mul (hQ l k) (h k) (norm_nonneg _) zero_le_one
    _ = 1 := one_mul 1

theorem matNorm_mul_of_integral {C : Type} [NormedField C] [IsUltrametricDist C] {r : ℕ}
    (Q Q' N : Matrix (Fin r) (Fin r) C) (hQQ : Q' * Q = 1) (hQ : ∀ l k, ‖Q l k‖ ≤ 1)
    (hQ' : ∀ l k, ‖Q' l k‖ ≤ 1) (i : Fin r) : matNorm (Q * N) i = matNorm N i := by
  unfold matNorm
  congr 1
  ext t
  constructor
  · rintro ⟨cf, h1, h2, h3, rfl⟩
    refine ⟨cf, h1, h2, ?_, rfl⟩
    have := integral_comb_mul Q' (Q * N) hQ' cf h3
    rwa [← Matrix.mul_assoc, hQQ, Matrix.one_mul] at this
  · rintro ⟨cf, h1, h2, h3, rfl⟩
    exact ⟨cf, h1, h2, integral_comb_mul Q N hQ cf h3, rfl⟩

theorem gl_invariant : ∀ {C : Type} [NormedField C] [IsUltrametricDist C] {r : ℕ} (Q Q' N : Matrix (Fin r) (Fin r) C),
    Q' * Q = 1 → (∀ l k, ‖Q l k‖ ≤ 1) → (∀ l k, ‖Q' l k‖ ≤ 1) → ∀ i, matNorm (Q * N) i = matNorm N i :=
  fun Q Q' N hQQ hQ hQ' i => matNorm_mul_of_integral Q Q' N hQQ hQ hQ' i

end GlobalTheory.TriFrame

end
