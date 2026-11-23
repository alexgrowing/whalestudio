import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaloisOfRegularForms
open IsDedekindDomain NumberField Formalism.UG Formalism.IndefR.Mult GlobalTheory.SphPar Polynomial

namespace GlobalTheory

theorem charpoly_smul_inv_of_charpoly_eq_prod (n : ℕ) (M : GL (Fin n) ℂ) (t : ℂ) (s : Multiset ℂ)
    (h : (M : Matrix (Fin n) (Fin n) ℂ).charpoly = (s.map fun a => X - C a).prod) :
    (t • ((M⁻¹ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ)).charpoly
      = (s.map fun a => X - C (t * a⁻¹)).prod := by
  set A : Matrix (Fin n) (Fin n) ℂ := (M : Matrix (Fin n) (Fin n) ℂ) with hA
  set B : Matrix (Fin n) (Fin n) ℂ := ((M⁻¹ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) with hB
  have hAB : A * B = 1 := by simp [hA, hB]
  have hcard : Multiset.card s = n := by
    have h1 := Matrix.charpoly_natDegree_eq_dim A
    rw [h, Polynomial.natDegree_multiset_prod_X_sub_C_eq_card] at h1
    simpa using h1
  have hev : ∀ y : ℂ, (Matrix.scalar (Fin n) y - A).det = (s.map fun a => y - a).prod := by
    intro y
    rw [← Matrix.eval_charpoly, h, Polynomial.eval_multiset_prod, Multiset.map_map]
    simp
  have hdet : A.det * B.det = 1 := by rw [← Matrix.det_mul, hAB, Matrix.det_one]
  have hneg : (-A).det = (s.map fun a => -a).prod := by simpa using hev 0
  have hne : (-A).det ≠ 0 := by
    rw [Matrix.det_neg]
    exact mul_ne_zero (pow_ne_zero _ (by norm_num)) (left_ne_zero_of_mul_eq_one hdet)
  have hs : ∀ a ∈ s, a ≠ 0 := by
    intro a ha h0
    apply hne
    rw [hneg]
    exact Multiset.prod_eq_zero (Multiset.mem_map.2 ⟨a, ha, by simp [h0]⟩)
  apply Polynomial.eq_of_infinite_eval_eq
  refine Set.Infinite.mono (s := ({0} : Set ℂ)ᶜ) ?_ (Set.finite_singleton _).infinite_compl
  intro x hx
  have hx0 : x ≠ 0 := hx
  simp only [Set.mem_setOf_eq]
  rw [Matrix.eval_charpoly, Polynomial.eval_multiset_prod, Multiset.map_map]
  apply mul_left_cancel₀ hne
  have key : (-A) * (Matrix.scalar (Fin n) x - t • B)
      = x • (Matrix.scalar (Fin n) (t / x) - A) := by
    rw [Matrix.scalar_apply, Matrix.scalar_apply, ← Matrix.smul_one_eq_diagonal,
      ← Matrix.smul_one_eq_diagonal, mul_sub, Matrix.mul_smul, Matrix.mul_smul, neg_mul, neg_mul, hAB, mul_one,
      smul_sub, smul_smul, mul_div_cancel₀ _ hx0, smul_neg, smul_neg]
    abel
  rw [← Matrix.det_mul, key, Matrix.det_smul, hev, hneg, ← Multiset.prod_map_mul, Fintype.card_fin,
    ← hcard, ← Multiset.prod_replicate, ← Multiset.map_const', ← Multiset.prod_map_mul]
  congr 1
  apply Multiset.map_congr rfl
  intro a ha
  have := hs a ha
  simp only [Function.comp, eval_sub, eval_X, eval_C]
  field_simp
  ring

end GlobalTheory
