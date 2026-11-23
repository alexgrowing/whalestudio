import Mathlib
open MvPolynomial

namespace GlobalTheory

theorem dualProd_logDeriv_modSq : ∀ {K R : Type} [CommRing K] [CommRing R] [Algebra K R] (δ : Derivation K R R) {N : ℕ} (e f : Fin N → R) (I : Ideal R), (∀ i, δ (e i) = 0) → (∀ i, e i ^ 2 ∈ I) → δ (∏ i, (1 + e i * f i)) - (∏ i, (1 + e i * f i)) * ∑ i, e i * δ (f i) ∈ I := by
  intro K R _ _ _ δ N
  induction N with
  | zero => intro e f I _ _; simp
  | succ n ih =>
    intro e f I he he2
    rw [Fin.prod_univ_succ, Fin.sum_univ_succ]
    have h := ih (fun i => e i.succ) (fun i => f i.succ) I (fun i => he _) (fun i => he2 _)
    set P := ∏ i : Fin n, (1 + e i.succ * f i.succ)
    set S := ∑ i : Fin n, e i.succ * δ (f i.succ)
    have key : δ ((1 + e 0 * f 0) * P) - (1 + e 0 * f 0) * P * (e 0 * δ (f 0) + S)
        = (1 + e 0 * f 0) * (δ P - P * S) - e 0 ^ 2 * (f 0 * P * δ (f 0)) := by
      simp only [Derivation.leibniz, map_add, Derivation.map_one_eq_zero, he 0, smul_eq_mul]
      ring
    rw [key]
    exact I.sub_mem (I.mul_mem_left _ h) (I.mul_mem_right _ (he2 0))

end GlobalTheory
