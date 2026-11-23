import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnifAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PlaceConjugationPropertiesCmField
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalTwistContinuousInvolutionIntegralPropertiesStatement
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.ConjSelfRecip

open ComplexConjugate

theorem reverse_X_sub_C' (μ : ℂ) : (X - C μ : ℂ[X]).reverse = 1 - C μ * X := by
  have h1 : (1 : ℂ[X]).reverse = 1 := by simp only [reverse, natDegree_one, reflect_one, pow_zero]
  have hX : (X : ℂ[X]).reverse = 1 := by simpa [h1] using reverse_X_mul (1 : ℂ[X])
  rw [sub_eq_add_neg, ← C_neg, reverse_add_C, hX, natDegree_X, pow_one, C_neg, neg_mul, ← sub_eq_add_neg]

theorem prod_conj_reverse (s : Multiset ℂ) (hs : ∀ z ∈ s, ‖z‖ = 1) :
    (((s.map fun z => X - C z).prod).map (starRingEnd ℂ)).reverse =
      C (conj (((s.map fun z => X - C z).prod).coeff 0)) * (s.map fun z => X - C z).prod := by
  induction s using Multiset.induction_on with
  | empty => simp [reverse]
  | cons a s ih =>
    have hs' : ∀ z ∈ s, ‖z‖ = 1 := fun z hz => hs z (Multiset.mem_cons_of_mem hz)
    have ha : ‖a‖ = 1 := hs a (Multiset.mem_cons_self a s)
    have hca : conj a * a = 1 := by
      rw [Complex.conj_mul', ha]; simp
    rw [Multiset.map_cons, Multiset.prod_cons, Polynomial.map_mul, reverse_mul_of_domain, ih hs',
      mul_coeff_zero]
    have hlin : ((X - C a : ℂ[X]).map (starRingEnd ℂ)).reverse = C (-conj a) * (X - C a) := by
      rw [Polynomial.map_sub, map_X, map_C, reverse_X_sub_C']
      have hw : C (conj a) * C a = (1 : ℂ[X]) := by rw [← C_mul, hca, C_1]
      rw [C_neg]
      linear_combination (-1 : ℂ[X]) * hw
    have hc0 : (X - C a : ℂ[X]).coeff 0 = -a := by simp
    rw [hlin, hc0, map_mul, C_mul]
    simp only [map_neg]
    ring

end GlobalTheory.ConjSelfRecip

namespace GlobalTheory.ConjSelfRecip

open ComplexConjugate

theorem reverse_map_inj {R S : Type} [CommRing R] [CommRing S] (f : R →+* S)
    (hf : Function.Injective f) (Q : R[X]) : (Q.map f).reverse = Q.reverse.map f := by
  rw [reverse, reverse, natDegree_map_eq_of_injective hf, reflect_map]

theorem ell_conj_selfRecip : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (P : E[X]), P ∈ Ell E n →
    P.coeff 0 ≠ 0 ∧ C (IsCMField.complexConj E (P.coeff 0)) * P =
      (P.map (IsCMField.complexConj E).toRingEquiv.toRingHom).reverse := by
  intro E _ _ _ n P hP
  obtain ⟨hm, -, -, hroots⟩ := hP
  let τ : E →+* ℂ := Classical.choice inferInstance
  have hQm : (P.map τ).Monic := hm.map τ
  have hQ : ((P.map τ).roots.map fun z => X - C z).prod = P.map τ :=
    prod_multiset_X_sub_C_of_monic_of_roots_card_eq hQm IsAlgClosed.card_roots_eq_natDegree
  have hr : ∀ z ∈ (P.map τ).roots, ‖z‖ = 1 := hroots τ
  have key := prod_conj_reverse (P.map τ).roots hr
  rw [hQ] at key
  constructor
  · intro h0
    have h0' : (0 : ℂ) ∈ (P.map τ).roots := by
      rw [mem_roots hQm.ne_zero, IsRoot, ← coeff_zero_eq_eval_zero, coeff_map, h0, map_zero]
    have := hr 0 h0'
    simp at this
  · apply Polynomial.map_injective τ τ.injective
    have hcomp : τ.comp (IsCMField.complexConj E).toRingEquiv.toRingHom = (starRingEnd ℂ).comp τ := by
      ext x
      simp [IsCMField.complexEmbedding_complexConj]
    rw [Polynomial.map_mul, map_C, ← reverse_map_inj τ τ.injective, Polynomial.map_map, hcomp,
      ← Polynomial.map_map, key, coeff_map]
    congr 2
    simp [IsCMField.complexEmbedding_complexConj]

end GlobalTheory.ConjSelfRecip
