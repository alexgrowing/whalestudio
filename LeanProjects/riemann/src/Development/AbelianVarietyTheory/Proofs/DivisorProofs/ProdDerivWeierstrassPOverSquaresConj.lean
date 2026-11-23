import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DatumOfIsIntegersLattice
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.MulStableIntegral
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsDiscreteValuationRingValuationSubringAtPrime
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.AddMonoidHomEqZeroOfEventually
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsConjKernelMulStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SqrtNegPrimeKernelCyclicStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CardSqModPrimeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProdDerivWeierstrassPOverSquaresNeZeroStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonzeroSquaresModPrimeMulPermUpToSignStatement
open NumberField IsDedekindDomain WeierstrassCurve GlobalTheory GlobalTheory.Published GlobalTheory.CMModel Formalism.L2.Th1.F
open scoped IntermediateField BigOperators Topology

noncomputable section

namespace GlobalTheory.SqConj

lemma wp_eq_of_sub_mem (L : PeriodPair) {z w : ℂ} (h : z - w ∈ L.lattice) :
    L.weierstrassP z = L.weierstrassP w := by
  have := L.weierstrassP_add_coe w ⟨z - w, h⟩
  simpa using this

lemma dwp_eq_of_sub_mem (L : PeriodPair) {z w : ℂ} (h : z - w ∈ L.lattice) :
    L.derivWeierstrassP z = L.derivWeierstrassP w := by
  have := L.derivWeierstrassP_add_coe w ⟨z - w, h⟩
  simpa using this

theorem sqProd_conj : ∀ (p : ℕ) (F : IntermediateField ℚ ℂ) (L : PeriodPair) (t : ℂ), p.Prime → p % 4 = 3 → 3 < p → Datum p F L t → ∀ σ : ℂ ≃+* ℂ, (∀ x ∈ F, σ x = x) → (σ (sqProd p L t) = sqProd p L t ∧ ∃ e : Sq p ≃ Sq p, ∀ k, GlobalTheory.ConjPoint.IsConj L L σ (sqPt p t k) (sqPt p t (e k))) ∨ σ (sqProd p L t) = -sqProd p L t := by
  intro p F L t hp hp4 hp3 hD σ hσ
  obtain ⟨c, hpc, hc⟩ := GlobalTheory.T.exists_conj_kernel_mul' p F L t hp hp4 hp3 hD σ hσ
  obtain ⟨e, ε, hε, he⟩ := GlobalTheory.T.nonzeroSquaresModPrime_mul_perm_up_to_sign p c hp hp4 hpc
  have hker := (GlobalTheory.T.sqrtNegPrime_kernel_cyclic p F L t hp hp4 hp3 hD).1
  obtain ⟨hne, -⟩ := GlobalTheory.T.prodDerivWeierstrassPOverSquares_ne_zero p F L t hp hp4 hp3 hD
  obtain ⟨-, hodd⟩ := GlobalTheory.T.two_mul_card_sq_add_one_eq_and_odd_of_mod_four_eq_three p hp hp4
  have hmem : ∀ k : Sq p, ((k.1 : ℕ) : ℂ) * ((c : ℂ) * t) - (ε : ℂ) * sqPt p t (e k) ∈ L.lattice := by
    intro k
    have := (hker _).2 (he k)
    convert this using 1
    simp only [sqPt]
    push_cast
    ring
  have hconj : ∀ k : Sq p, ((k.1 : ℕ) : ℂ) * ((c : ℂ) * t) ∉ L.lattice ∧
      L.weierstrassP (((k.1 : ℕ) : ℂ) * ((c : ℂ) * t)) = σ (L.weierstrassP (sqPt p t k)) ∧
      L.derivWeierstrassP (((k.1 : ℕ) : ℂ) * ((c : ℂ) * t)) = σ (L.derivWeierstrassP (sqPt p t k)) := by
    intro k
    rcases hc k.1 with h | h
    · exact absurd h.1 (hne k).1
    · exact ⟨h.2.1, h.2.2.1, h.2.2.2⟩
  have hσprod : σ (sqProd p L t) = ∏ k : Sq p, L.derivWeierstrassP (((k.1 : ℕ) : ℂ) * ((c : ℂ) * t)) := by
    simp only [sqProd, map_prod]
    exact Finset.prod_congr rfl fun k _ => (hconj k).2.2.symm
  rcases hε with rfl | rfl
  · left
    have hm : ∀ k : Sq p, ((k.1 : ℕ) : ℂ) * ((c : ℂ) * t) - sqPt p t (e k) ∈ L.lattice := by
      intro k; simpa using hmem k
    refine ⟨?_, e, fun k => ?_⟩
    · rw [hσprod]
      simp only [dwp_eq_of_sub_mem L (hm _)]
      exact Equiv.prod_comp e (fun k => L.derivWeierstrassP (sqPt p t k))
    · right
      refine ⟨(hne k).1, (hne (e k)).1, ?_, ?_⟩
      · rw [← wp_eq_of_sub_mem L (hm k)]; exact (hconj k).2.1
      · rw [← dwp_eq_of_sub_mem L (hm k)]; exact (hconj k).2.2
  · right
    have hm : ∀ k : Sq p, ((k.1 : ℕ) : ℂ) * ((c : ℂ) * t) - (-sqPt p t (e k)) ∈ L.lattice := by
      intro k; simpa using hmem k
    rw [hσprod]
    simp only [dwp_eq_of_sub_mem L (hm _), PeriodPair.derivWeierstrassP_neg]
    rw [Finset.prod_neg, Equiv.prod_comp e (fun k => L.derivWeierstrassP (sqPt p t k)),
      Finset.card_univ, hodd.neg_one_pow, sqProd]
    ring

end GlobalTheory.SqConj
