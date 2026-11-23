import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.WignerHighestWeights.IsAlgIsoRefl
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.DualInfinitesimalCharacterRegular
open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.AlgRepEndIrreducible
open scoped TensorProduct

namespace UpperTheory.V.AlgRepEndIrreducible.GLNegationOpposite

open Formalism.REAL Formalism.HermitianLatticeCounting.P MulOpposite

variable {A : Type} [Ring A] [Algebra ℂ A] {n : ℕ}

omit [Algebra ℂ A] in

private theorem glRel_op {X : Fin n → Fin n → A} (h : Formalism.REAL.GlRel X) : Formalism.REAL.GlRel fun i j => op (X j i) := by
  intro a b c d
  have h1 := congrArg op (h d c b a)
  simp only [op_sub, op_mul, apply_ite op, op_zero] at h1
  rw [h1]
  simp only [eq_comm (a := c) (b := b), eq_comm (a := a) (b := d)]

private theorem qdet_op {X : Fin n → Fin n → A} (h : Formalism.REAL.GlRel X) (y : ℂ) :
    qdet (fun i j => op (X j i)) y = op (qdet X y) := by
  have hP : ∀ (arg : Fin n → ℂ) (σ τ : Equiv.Perm (Fin n)), orderedTermProduct (fun i j => op (X j i)) arg σ τ =
      op (orderedTermProduct X (arg ∘ Fin.revPerm) (τ * Fin.revPerm) (σ * Fin.revPerm)) := fun arg σ τ => by
    unfold orderedTermProduct
    rw [op_list_prod, List.map_ofFn]
    congr 1
    refine List.ext_getElem (by simp) fun k h1 h2 => ?_
    have hk : k < n := by simpa using h1
    have e : (⟨n - 1 - k, by omega⟩ : Fin n).rev = ⟨k, hk⟩ := Fin.ext (by rw [Fin.val_rev]; simp only; omega)
    simp only [List.getElem_reverse, List.getElem_ofFn, List.length_ofFn, Function.comp_apply, Equiv.Perm.mul_apply,
      Fin.revPerm_apply, e, Tm, op_add, apply_ite op, op_zero, eq_comm (a := τ _)]
    rfl
  have hS : ∀ arg : Fin n → ℂ, doublyAntisymmetrizedProduct (fun i j => op (X j i)) arg = op (doublyAntisymmetrizedProduct X (arg ∘ Fin.revPerm)) := fun arg => by
    unfold doublyAntisymmetrizedProduct
    rw [Finset.sum_comm, Finset.op_sum]
    refine Fintype.sum_equiv (Equiv.mulRight Fin.revPerm) _ _ fun σ => ?_
    rw [Finset.op_sum]
    refine Fintype.sum_equiv (Equiv.mulRight Fin.revPerm) _ _ fun τ => ?_
    simp only [hP, ← zsmul_eq_mul, op_smul, smul_smul, Equiv.coe_mulRight, Equiv.Perm.sign_mul, Units.val_mul]
    congr 1
    linear_combination (-((Equiv.Perm.sign σ : ℤ) * (Equiv.Perm.sign τ : ℤ))) *
      Int.units_coe_mul_self (Equiv.Perm.sign (Fin.revPerm (n := n)))
  have e := hS fun k => y - (k : ℂ)
  rw [antisymmetrizedProduct_perm_invariant, antisymmetrizedProduct_eq_factorial_smul_qdet _ h, antisymmetrizedProduct_eq_factorial_smul_qdet _ (glRel_op h), op_smul] at e
  exact (IsUnit.mk0 _ (by exact_mod_cast n.factorial_ne_zero)).smul_left_cancel.mp e

private theorem qdet_antipode {X : Fin n → Fin n → A} (h : Formalism.REAL.GlRel X) (x : ℂ) :
    qdet (fun i j => -op (X i j)) x = op ((-1 : ℂ) ^ n • qdet X ((n : ℂ) - 1 - x)) := by
  rw [quantumDet_neg_transpose _ (glRel_op h), qdet_op h, op_smul]

omit [Algebra ℂ A] in

private theorem glRel_negOp {X : Fin n → Fin n → A} (h : Formalism.REAL.GlRel X) :
    Formalism.REAL.GlRel fun i j => -op (X i j) := by
  intro a b c d
  have h1 := congrArg op (h c d a b)
  simp only [op_sub, op_mul, apply_ite op, op_zero] at h1
  simp only [neg_mul_neg]
  rw [h1]
  simp only [eq_comm (a := d) (b := a), eq_comm (a := b) (b := c)]
  split_ifs <;> abel

end UpperTheory.V.AlgRepEndIrreducible.GLNegationOpposite

theorem UpperTheory.V.AlgRepEndIrreducible.glNegOp :
    ∀ (A : Type) [Ring A] [Algebra ℂ A] (n : ℕ) (X : Fin n → Fin n → A), Formalism.REAL.GlRel X →
      Formalism.REAL.GlRel (fun i j => -MulOpposite.op (X i j)) ∧
      ∀ x : ℂ, Formalism.REAL.qdet (fun i j => -MulOpposite.op (X i j)) x =
        MulOpposite.op ((-1 : ℂ) ^ n • Formalism.REAL.qdet X ((n : ℂ) - 1 - x)) :=
  fun _ _ _ _ _ h => ⟨GLNegationOpposite.glRel_negOp h, fun x => GLNegationOpposite.qdet_antipode h x⟩
