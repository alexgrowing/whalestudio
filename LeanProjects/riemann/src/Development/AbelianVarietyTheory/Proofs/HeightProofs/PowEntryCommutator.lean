import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsLieDataCircle

namespace GlobalTheory.PowEntryCommutator

open Matrix

theorem pow_entry_commutator {A : Type} [Ring A] {n : ℕ} (E : Fin n → Fin n → A)
    (hE : Formalism.REAL.GlRel E) (a b : Fin n) (m : ℕ) (c e : Fin n) :
    E a b * ((Matrix.of E) ^ m) c e - ((Matrix.of E) ^ m) c e * E a b =
      (if b = c then ((Matrix.of E) ^ m) a e else 0) -
        (if e = a then ((Matrix.of E) ^ m) c b else 0) := by
  induction m generalizing c e with
  | zero =>
    clear hE
    simp only [pow_zero, Matrix.one_apply]
    by_cases h1 : c = e <;> by_cases h2 : b = c <;> by_cases h3 : e = a <;>
      simp only [h1, h2, h3, if_true, if_false, mul_one, one_mul, mul_zero, zero_mul, sub_self] <;>
      subst_vars <;> simp_all <;> intro h <;> subst h <;> simp_all
  | succ m ih =>
    have hs : ∀ x y : Fin n, ((Matrix.of E) ^ (m + 1)) x y
        = ∑ k, ((Matrix.of E) ^ m) x k * E k y := by
      intro x y; rw [pow_succ, Matrix.mul_apply]; rfl
    have key : ∀ k, E a b * (((Matrix.of E) ^ m) c k * E k e)
          - ((Matrix.of E) ^ m) c k * E k e * E a b
        = (E a b * ((Matrix.of E) ^ m) c k - ((Matrix.of E) ^ m) c k * E a b) * E k e
          + ((Matrix.of E) ^ m) c k * (E a b * E k e - E k e * E a b) := by
      intro k; noncomm_ring
    rw [hs, hs, hs, Finset.mul_sum, Finset.sum_mul, ← Finset.sum_sub_distrib]
    simp_rw [key, ih, hE a b]
    simp only [sub_mul, mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib, ite_mul, mul_ite,
      zero_mul, mul_zero, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true,
      Finset.sum_const_zero]
    split_ifs <;> simp [Finset.sum_sub_distrib] <;> abel

theorem target : ∀ {A : Type} [inst : Ring A] {n : ℕ} (E : Fin n → Fin n → A), Formalism.REAL.GlRel E →
    ∀ (a b : Fin n) (m : ℕ) (c e : Fin n),
    E a b * ((Matrix.of : (Fin n → Fin n → A) → Matrix (Fin n) (Fin n) A) E ^ m) c e -
      ((Matrix.of : (Fin n → Fin n → A) → Matrix (Fin n) (Fin n) A) E ^ m) c e * E a b =
    (if b = c then ((Matrix.of : (Fin n → Fin n → A) → Matrix (Fin n) (Fin n) A) E ^ m) a e
      else (0 : A)) -
    if e = a then ((Matrix.of : (Fin n → Fin n → A) → Matrix (Fin n) (Fin n) A) E ^ m) c b
      else (0 : A) :=
  fun E hE a b m c e => pow_entry_commutator E hE a b m c e

end GlobalTheory.PowEntryCommutator
