import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.InterPolyProdSum
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BlockSymApply
import ReciprocityTheory.DualLattices.DetPolyMulCayleyOmegaPow
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BlockGraph
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TopDegreeFormCoeffRenameCayleyBlockSymbolEmbeddiStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CayleyOperatorPowEqSignedSumPartialDerivsStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ConstantCoeffCayleyOperatorPowDeterminantPowStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CoeffComposedPartialDerivListOfNodupStatement

set_option autoImplicit false

noncomputable section

open MvPolynomial ReciprocityTheory.PGsh

namespace GlobalTheory.CayleyBlock

theorem det_pow_eq {p q : ℕ} (h1 : Fintype.card (Unit × Fin p × Fin q) = p * q) :
    (GlobalTheory.DomainDens.blockSym h1 ()).det ^ q = rename (blockEmb h1) (sumMap p q (cayDet p ℂ ^ q)) := by
  rw [map_pow, map_pow, cayDet, AlgHom.map_det, AlgHom.map_det]
  congr 2
  ext i j
  simp [GlobalTheory.DomainDens.blockSym_apply, sumMap, blockEmb, Matrix.mvPolynomialX]

theorem bigList_nodup {p q : ℕ} (τ : Fin q → Equiv.Perm (Fin p)) : (bigList τ).Nodup := by
  rw [bigList, List.nodup_flatMap]
  refine ⟨fun b _ => (List.nodup_finRange p).map fun j k h => by simpa using congrArg (fun x => x.2.2) h, ?_⟩
  refine (List.nodup_finRange q).imp fun {a b} hab => ?_
  show List.Disjoint _ _
  rw [List.disjoint_left]
  intro x hx hy
  simp only [List.mem_map, List.mem_finRange, true_and] at hx hy
  obtain ⟨j, rfl⟩ := hx
  obtain ⟨k, hk⟩ := hy
  exact hab (congrArg Prod.fst hk).symm

theorem bigList_sum {p q : ℕ} (τ : Fin q → Equiv.Perm (Fin p)) :
    ((bigList τ).map fun v => Finsupp.single v 1).sum = blockGraph τ := by
  simp [bigList, blockGraph, List.map_flatMap, Fin.sum_univ_def, List.map_map, Function.comp_def]
  simp [List.flatMap, List.sum_flatten, List.map_map, Function.comp_def]

theorem pderiv_sumMap {p q : ℕ} (v : Fin q × Fin p × Fin p) (P : MvPolynomial (Fin p × Fin p) ℂ) :
    pderiv v (sumMap p q P) = sumMap p q (pderiv v.2 P) := by
  induction P using MvPolynomial.induction_on with
  | C a => simp [sumMap]
  | add f g hf hg => simp only [map_add, hf, hg]
  | mul_X f w hf =>
    simp only [map_mul, Derivation.leibniz, hf, smul_eq_mul, map_add]
    congr 1
    simp [sumMap, pderiv_X, Pi.single_apply, Prod.ext_iff]
    by_cases h : w.1 = v.2.1 ∧ w.2 = v.2.2 <;> simp [h, Finset.filter_eq']

theorem dList_sumMap {p q : ℕ} (l : List (Fin q × Fin p × Fin p)) (P : MvPolynomial (Fin p × Fin p) ℂ) :
    dList l (sumMap p q P) = sumMap p q (dList (l.map fun v => v.2) P) := by
  induction l with
  | nil => simp [dList]
  | cons v l ih =>
    simp only [dList, List.map_cons, List.prod_cons, Module.End.mul_apply] at ih ⊢
    rw [ih]
    exact pderiv_sumMap v _

theorem bigList_map {p q : ℕ} (τ : Fin q → Equiv.Perm (Fin p)) : (bigList τ).map (fun v => v.2) = smallList τ := by
  simp [bigList, smallList, List.map_flatMap, List.map_map, Function.comp_def]

theorem constantCoeff_sumMap (p q : ℕ) (P : MvPolynomial (Fin p × Fin p) ℂ) :
    constantCoeff (sumMap p q P) = constantCoeff P := by
  induction P using MvPolynomial.induction_on with
  | C a => simp [sumMap]
  | add f g hf hg => simp only [map_add, hf, hg]
  | mul_X f w hf => simp [sumMap, constantCoeff_X]

end GlobalTheory.CayleyBlock

open GlobalTheory.CayleyBlock ReciprocityTheory.PGsh MvPolynomial in

theorem GlobalTheory.topCoeff_blockSym_det_pow : ∀ (p q : ℕ) (h1 : Fintype.card (Unit × Fin p × Fin q) = p * q),
    GlobalTheory.GoodMetric.topCoeff ((GlobalTheory.DomainDens.blockSym h1 ()).det ^ q) =
      ∏ i ∈ Finset.range p, (((q + i).factorial : ℂ) / i.factorial) := by
  intro p q h1
  rw [det_pow_eq, GlobalTheory.T.topDegreeFormCoeff_rename_cayleyBlockSymbolEmbedding, ← GlobalTheory.T.constantCoeff_cayleyOperator_pow_determinant_pow, GlobalTheory.T.cayleyOperator_pow_eq_signed_sum_partialDerivs, LinearMap.sum_apply]
  have key : ∀ τ : Fin q → Equiv.Perm (Fin p), (sgnProd τ : ℂ) * coeff (blockGraph τ) (sumMap p q (cayDet p ℂ ^ q)) =
      constantCoeff (sgnProd τ • dList (smallList τ) (cayDet p ℂ ^ q)) := by
    intro τ
    rw [← bigList_sum, ← zero_add ((bigList τ).map _).sum, ← GlobalTheory.T.coeff_composedPartialDerivList_of_nodup _ (bigList_nodup τ) 0 (fun _ _ => rfl),
      dList_sumMap, bigList_map, ← constantCoeff_sumMap p q, map_zsmul, zsmul_eq_mul,
      ← map_intCast (C : ℂ →+* MvPolynomial (Fin q × Fin p × Fin p) ℂ), map_mul, constantCoeff_C, constantCoeff_eq]
  simp_rw [LinearMap.smul_apply, key, map_sum]
