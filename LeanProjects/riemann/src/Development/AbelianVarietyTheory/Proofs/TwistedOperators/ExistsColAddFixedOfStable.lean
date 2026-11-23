import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.IrreducibleDistinctUnitary
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GenericDetPowMulHw
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.NonemptyDirectSumEquivOfFinrankLe
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsSemisimpleRepresentationTprodOfIsIrreducibleAl
open MvPolynomial Formalism.BasicNotions Formalism.GradedWeylDivisibility GlobalTheory.Branching GlobalTheory.GLDuality
open Formalism.REAL (fockF)
open scoped DirectSum TensorProduct Kronecker Matrix

namespace GlobalTheory.GLDuality

theorem rename_swap_matRep_one_right {n n' : ℕ} (g : GL (Fin n) ℂ) (v : MvPolynomial (Fin n' × Fin n) ℂ) :
    rename Prod.swap (matRep n n' (g, 1) v) =
      rowAct ℂ (g : Matrix (Fin n) (Fin n) ℂ)ᵀ (rename Prod.swap v) := by
  have : (rename (R := ℂ) (Prod.swap : Fin n' × Fin n → Fin n × Fin n')).comp
      (sub (((1 : GL (Fin n') ℂ) : Matrix (Fin n') (Fin n') ℂ) ⊗ₖ (g : Matrix (Fin n) (Fin n) ℂ))ᵀ) =
      (rowAct ℂ (g : Matrix (Fin n) (Fin n) ℂ)ᵀ).comp (rename Prod.swap) := by
    apply MvPolynomial.algHom_ext
    rintro ⟨a, s⟩
    simp [sub, rowAct, Fintype.sum_prod_type, Matrix.one_apply, apply_ite C]
  rw [matRep_apply]
  exact DFunLike.congr_fun this v

theorem rename_swap_colAdd {n n' : ℕ} (l j : Fin n) (c : ℂ) (v : MvPolynomial (Fin n' × Fin n) ℂ) :
    rename Prod.swap (colAdd ℂ l j c v) =
      Polynomial.eval (C c) (rowGen ℂ l j (rename Prod.swap v)) := by
  induction v using MvPolynomial.induction_on with
  | C a => simp [colAdd, rowGen]
  | add p q hp hq => simp only [map_add, hp, hq, Polynomial.eval_add]
  | mul_X p v hp =>
    obtain ⟨a, s⟩ := v
    simp only [map_mul, hp, Polynomial.eval_mul]
    congr 1
    by_cases h : s = j <;> simp [colAdd, rowGen, h, mul_comm (C c)]

theorem rowGen_coeff_zero_eq {r n : ℕ} (a b : Fin r) (f : MvPolynomial (Fin r × Fin n) ℂ) :
    (rowGen ℂ a b f).coeff 0 = f := by
  rw [Polynomial.coeff_zero_eq_eval_zero]
  induction f using MvPolynomial.induction_on with
  | C a => simp [rowGen]
  | add p q hp hq => simp only [map_add, hp, hq, Polynomial.eval_add]
  | mul_X p v hp =>
    simp only [map_mul, hp, Polynomial.eval_mul]
    congr 1
    by_cases h : v.1 = b <;> simp [rowGen, h]

theorem exists_colAdd_fixed_of_stable (n n' : ℕ) (N : Submodule ℂ (MvPolynomial (Fin n' × Fin n) ℂ)) (hN : N ≠ ⊥)
    (hst : ∀ g : GL (Fin n) ℂ, ∀ v ∈ N, matRep n n' (g, 1) v ∈ N) :
    ∃ v ∈ N, v ≠ 0 ∧ ∀ l j : Fin n, l < j → ∀ c : ℂ, colAdd ℂ l j c v = v := by
  have hinj : Function.Injective
      (rename (R := ℂ) (Prod.swap : Fin n' × Fin n → Fin n × Fin n')) :=
    rename_injective _ Prod.swap_injective
  let M : Submodule ℂ (MvPolynomial (Fin n × Fin n') ℂ) :=
    N.map (rename (R := ℂ) (Prod.swap : Fin n' × Fin n → Fin n × Fin n')).toLinearMap
  have hU : ∀ u ∈ Matrix.unitaryGroup (Fin n) ℂ, ∀ f ∈ M, rowAct ℂ u f ∈ M := by
    rintro u hu _ ⟨f, hf, rfl⟩
    let t : Matrix.unitaryGroup (Fin n) ℂ := Matrix.UnitaryGroup.transpose ⟨u, hu⟩
    exact ⟨_, hst (unitaryIncl n t) f hf, rename_swap_matRep_one_right (unitaryIncl n t) f⟩
  have hcl := rowDivClosed_of_rowAct_stable M (rowAct_mem_of_unitary_stable M hU)
  have hne : M ≠ ⊥ := fun e => hN (Submodule.map_injective_of_injective hinj
    (e.trans (Submodule.map_bot _).symm))
  obtain ⟨_, ⟨v, hv, rfl⟩, hv0, hkill⟩ := exists_killed_of_rowDivClosed M hcl hne
  refine ⟨v, hv, fun e => hv0 (by rw [e, map_zero]), fun l j hlj c => hinj ?_⟩
  have hC : rowGen ℂ l j (rename Prod.swap v) = Polynomial.C (rename Prod.swap v) := by
    ext1 k
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · rw [rowGen_coeff_zero_eq, Polynomial.coeff_C_zero]
    · rw [Polynomial.coeff_C_of_ne_zero hk.ne']
      exact hkill l j hlj k hk
  rw [rename_swap_colAdd, hC, Polynomial.eval_C]

end GlobalTheory.GLDuality
