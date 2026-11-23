import Formalism.LocalToGlobal.Columns.CoefficientsModP.NablaIndependenceHolds
import Formalism.LocalToGlobal.Columns.CoefficientsModP.TauLatticeLatticeHolds

open MvPolynomial NumberField IsDedekindDomain
open scoped Matrix

noncomputable section

namespace Formalism.L2.DIV

open Formalism.BasicNotions

section Dual

variable {K : Type} [Field K] [NumberField K] {n : ℕ}

end Dual

section Tensor

variable {K : Type} [Field K] {ι : Type} [Fintype ι] {n : ℕ}

def rdSq (lam : DomWeight n) (g : GL (Fin n) K) :
    MvPolynomial (Fin n × Fin n) K →ₗ[K] MvPolynomial (Fin n × Fin n) K :=
  detPow K n g lam.detShift • (Formalism.GradedWeylDivisibility.rowAct K (n := n) (g : Matrix (Fin n) (Fin n) K)ᵀ).toLinearMap

theorem rd_rowAct_one (f : MvPolynomial (Fin n × Fin n) K) :
    Formalism.GradedWeylDivisibility.rowAct K (1 : Matrix (Fin n) (Fin n) K) f = f := by
  have h : Formalism.GradedWeylDivisibility.rowAct K (n := n) (1 : Matrix (Fin n) (Fin n) K) = AlgHom.id K _ := by
    apply MvPolynomial.algHom_ext
    intro v
    simp only [Formalism.GradedWeylDivisibility.rowAct, aeval_X, Matrix.one_apply, AlgHom.id_apply]
    rw [Finset.sum_eq_single v.1]
    · simp
    · intro b _ hb
      simp [Ne.symm hb]
    · simp
  rw [h]; rfl

theorem rd_rowAct_rowAct (g h : Matrix (Fin n) (Fin n) K) (f : MvPolynomial (Fin n × Fin n) K) :
    Formalism.GradedWeylDivisibility.rowAct K g (Formalism.GradedWeylDivisibility.rowAct K h f) = Formalism.GradedWeylDivisibility.rowAct K (h * g) f := by
  rw [← Formalism.GradedWeylDivisibility.rowActMul K n n g h]; rfl

end Tensor

end Formalism.L2.DIV
