import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnifAt
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.ResConj

theorem prod_product_mul (A B : Multiset ℂ) (f g : ℂ → ℂ) :
    ((A ×ˢ B).map fun ij => f ij.1 * g ij.2).prod =
      (A.map f).prod ^ Multiset.card B * (B.map g).prod ^ Multiset.card A := by
  induction A using Multiset.induction_on with
  | empty => simp
  | cons a A ih =>
    rw [Multiset.cons_product, Multiset.map_add, Multiset.prod_add, ih, Multiset.map_map]
    simp only [Function.comp_def, Multiset.prod_map_mul, Multiset.map_const', Multiset.prod_replicate,
      Multiset.map_cons, Multiset.prod_cons, Multiset.card_cons, mul_pow, pow_succ]
    ring

theorem conj_prod_sub (A B : Multiset ℂ) (hA : ∀ x ∈ A, ‖x‖ = 1) (hB : ∀ y ∈ B, ‖y‖ = 1) :
    (starRingEnd ℂ) (((A ×ˢ B).map fun ij => ij.1 - ij.2).prod) *
        (A.prod ^ Multiset.card B * B.prod ^ Multiset.card A) =
      (-1) ^ (Multiset.card A * Multiset.card B) * ((A ×ˢ B).map fun ij => ij.1 - ij.2).prod := by
  have h := prod_product_mul A B id id
  simp only [Multiset.map_id, id, Multiset.map_id'] at h
  rw [← h, map_multiset_prod, Multiset.map_map, ← Multiset.prod_map_mul]
  have hc : ∀ ij ∈ A ×ˢ B, ((starRingEnd ℂ) ∘ fun ij : ℂ × ℂ => ij.1 - ij.2) ij * (ij.1 * ij.2) =
      (-1) * (ij.1 - ij.2) := by
    intro ij hij
    rw [Multiset.mem_product] at hij
    have h1 := hA _ hij.1
    have h2 := hB _ hij.2
    have n1 : ij.1 ≠ 0 := by intro h0; rw [h0, norm_zero] at h1; exact zero_ne_one h1
    have n2 : ij.2 ≠ 0 := by intro h0; rw [h0, norm_zero] at h2; exact zero_ne_one h2
    have c1 : (starRingEnd ℂ) ij.1 = ij.1⁻¹ := by
      rw [Complex.inv_def, Complex.normSq_eq_norm_sq, h1]; simp
    have c2 : (starRingEnd ℂ) ij.2 = ij.2⁻¹ := by
      rw [Complex.inv_def, Complex.normSq_eq_norm_sq, h2]; simp
    simp only [Function.comp_apply, map_sub, c1, c2]
    field_simp
    ring
  rw [Multiset.map_congr rfl hc, Multiset.prod_map_mul, Multiset.map_const', Multiset.prod_replicate,
    Multiset.card_product]

theorem conj_resultant : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a b : ℕ) (P₁ P₂ : E[X]),
    P₁ ∈ Ell E a → P₂ ∈ Ell E b → IsCMField.complexConj E (resultant P₁ P₂) *
      (((-1) ^ a * P₁.coeff 0) ^ b * ((-1) ^ b * P₂.coeff 0) ^ a) = (-1) ^ (a * b) * resultant P₁ P₂ := by
  intro E _ _ _ a b P₁ P₂ h₁ h₂
  obtain ⟨m₁, d₁, -, r₁⟩ := h₁
  obtain ⟨m₂, d₂, -, r₂⟩ := h₂
  let τ : E →+* ℂ := Classical.choice (inferInstance : Nonempty (E →+* ℂ))
  apply τ.injective
  have sA : (P₁.map τ).Splits := IsAlgClosed.splits _
  have sB : (P₂.map τ).Splits := IsAlgClosed.splits _
  have cA : Multiset.card (P₁.map τ).roots = a := by rw [← sA.natDegree_eq_card_roots, natDegree_map, d₁]
  have cB : Multiset.card (P₂.map τ).roots = b := by rw [← sB.natDegree_eq_card_roots, natDegree_map, d₂]
  have hres : τ (resultant P₁ P₂) =
      (((P₁.map τ).roots ×ˢ (P₂.map τ).roots).map fun ij => ij.1 - ij.2).prod := by
    rw [← resultant_eq_prod_roots_sub _ _ (m₁.map τ) (m₂.map τ) sA sB,
      ← resultant_map_map P₁ P₂ P₁.natDegree P₂.natDegree τ, natDegree_map, natDegree_map]
  have e₁ : τ ((-1) ^ a * P₁.coeff 0) = (P₁.map τ).roots.prod := by
    rw [map_mul, map_pow, map_neg, map_one, ← coeff_map, sA.coeff_zero_eq_prod_roots_of_monic (m₁.map τ),
      natDegree_map, d₁, ← mul_assoc, ← pow_add, ← two_mul, pow_mul, neg_one_sq, one_pow, one_mul]
  have e₂ : τ ((-1) ^ b * P₂.coeff 0) = (P₂.map τ).roots.prod := by
    rw [map_mul, map_pow, map_neg, map_one, ← coeff_map, sB.coeff_zero_eq_prod_roots_of_monic (m₂.map τ),
      natDegree_map, d₂, ← mul_assoc, ← pow_add, ← two_mul, pow_mul, neg_one_sq, one_pow, one_mul]
  have key := conj_prod_sub _ _ (r₁ τ) (r₂ τ)
  rw [cA, cB] at key
  rw [map_mul, map_mul, map_mul, map_pow, map_pow, e₁, e₂, IsCMField.complexEmbedding_complexConj, hres, key,
    map_pow, map_neg, map_one]

end GlobalTheory.ResConj
