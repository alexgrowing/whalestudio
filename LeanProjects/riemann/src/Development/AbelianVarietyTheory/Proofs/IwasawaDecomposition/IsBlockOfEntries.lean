import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StepZeroTwistReferenceTupleEqId
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.SplitLastBlockActX
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.TopStep Matrix
open Formalism.L2.Theta GlobalTheory.Mem.Th Filter Topology MeasureTheory
open GlobalTheory.Mem.ColAd GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2.TC
attribute [local instance] GlobalTheory.Mem.Col2.starE
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice
open scoped TensorProduct

namespace GlobalTheory.Mem.Col2.TC.BlockMatrixCriteria

theorem sum_ite_val {m : ℕ} (f : Fin m → ℂ) (c : ℕ) (hc : c < m) :
    ∑ j : Fin m, (if (j : ℕ) = c then f j else 0) = f ⟨c, hc⟩ := by
  rw [Finset.sum_eq_single ⟨c, hc⟩]
  · simp
  · intro j _ hj
    rw [if_neg]
    exact fun h => hj (Fin.ext h)
  · simp

theorem sum_ite_val_zero {m : ℕ} (f : Fin m → ℂ) (c : ℕ) (hc : m ≤ c) :
    ∑ j : Fin m, (if (j : ℕ) = c then f j else 0) = 0 :=
  Finset.sum_eq_zero fun j _ => if_neg (by have := j.2; omega)

theorem isBlock_of_frame {p q N n : ℕ} (hp : p = N) (hq : q = n) (hN : N = n + 1) (M : Matrix (Fin p) (Fin p) ℂ)
    (M' : Matrix (Fin q) (Fin q) ℂ)
    (h1 : M * Matrix.of (fun (i : Fin p) (a : Fin q) => if (i : ℕ) = a then (1 : ℂ) else 0) =
      Matrix.of (fun (i : Fin p) (a : Fin q) => if (i : ℕ) = a then (1 : ℂ) else 0) * M')
    (h2 : M *ᵥ (fun i : Fin p => if (i : ℕ) = q then (1 : ℂ) else 0) = fun i : Fin p => if (i : ℕ) = q then (1 : ℂ) else 0) :
    GlobalTheory.BranchFormula.IsBlock hN (fun i j : Fin N => M (Fin.cast hp.symm i) (Fin.cast hp.symm j))
      (fun a b : Fin n => M' (Fin.cast hq.symm a) (Fin.cast hq.symm b)) 1 := by
  subst hp hq hN
  refine ⟨fun a b => ?_, fun a => ⟨?_, ?_⟩, ?_⟩
  · have e := congrFun (congrFun h1 (Br.iC rfl a)) b
    simp only [Matrix.mul_apply, Matrix.of_apply, mul_ite, mul_one, mul_zero, ite_mul, one_mul, zero_mul] at e
    simp only [eq_comm (a := ((Br.iC rfl a : Fin (q+1)) : ℕ))] at e
    rw [sum_ite_val _ _ (by have := b.2; omega), sum_ite_val _ _ (show ((Br.iC rfl a : Fin (q+1)) : ℕ) < q from a.2)] at e
    exact e
  · have e := congrFun h2 (Br.iC rfl a)
    simp only [Matrix.mulVec, dotProduct, mul_ite, mul_one, mul_zero] at e
    rw [sum_ite_val _ _ (by omega), if_neg (by have := a.2; simp [Br.iC]; omega)] at e
    exact e
  · have e := congrFun (congrFun h1 (Br.iL rfl)) a
    simp only [Matrix.mul_apply, Matrix.of_apply, mul_ite, mul_one, mul_zero, ite_mul, one_mul, zero_mul] at e
    simp only [eq_comm (a := ((Br.iL rfl : Fin (q+1)) : ℕ))] at e
    rw [sum_ite_val _ _ (by have := a.2; omega), sum_ite_val_zero _ _ (by simp [Br.iL])] at e
    exact e
  · have e := congrFun h2 (Br.iL rfl)
    simp only [Matrix.mulVec, dotProduct, mul_ite, mul_one, mul_zero] at e
    rw [sum_ite_val _ _ (by omega), if_pos (by simp [Br.iL])] at e
    exact e

end GlobalTheory.Mem.Col2.TC.BlockMatrixCriteria

namespace GlobalTheory.Mem.Col2.TC.BlockMatrixCriteria

theorem isBlock_of_entries {p q N n : ℕ} (hp : p = N) (hq : q = n) (hN : N = n + 1) (M : Matrix (Fin p) (Fin p) ℂ)
    (M' : Matrix (Fin q) (Fin q) ℂ) (A : Matrix (Fin N) (Fin N) ℂ) (A' : Matrix (Fin n) (Fin n) ℂ)
    (hA : ∀ i j, A i j = M (Fin.cast hp.symm i) (Fin.cast hp.symm j))
    (hA' : ∀ i j, A' i j = M' (Fin.cast hq.symm i) (Fin.cast hq.symm j))
    (h1 : M * Matrix.of (fun (i : Fin p) (a : Fin q) => if (i : ℕ) = a then (1 : ℂ) else 0) =
      Matrix.of (fun (i : Fin p) (a : Fin q) => if (i : ℕ) = a then (1 : ℂ) else 0) * M')
    (h2 : M *ᵥ (fun i : Fin p => if (i : ℕ) = q then (1 : ℂ) else 0) = fun i : Fin p => if (i : ℕ) = q then (1 : ℂ) else 0) :
    GlobalTheory.BranchFormula.IsBlock hN A A' 1 := by
  have e1 : A = fun i j => M (Fin.cast hp.symm i) (Fin.cast hp.symm j) := funext fun i => funext fun j => hA i j
  have e2 : A' = fun i j => M' (Fin.cast hq.symm i) (Fin.cast hq.symm j) := funext fun i => funext fun j => hA' i j
  subst e1 e2
  exact isBlock_of_frame hp hq hN M M' h1 h2

end GlobalTheory.Mem.Col2.TC.BlockMatrixCriteria

namespace GlobalTheory.Mem.Col2.TC

end GlobalTheory.Mem.Col2.TC
