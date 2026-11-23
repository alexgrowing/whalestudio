import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.StatementsThroughPointIncIdeal
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section

theorem ThroughPointIncIdeal.eval_aeval {F K : Type*} [Field F] [Field K] [Algebra F K] {σ τ : Type*}
    (s : σ → MvPolynomial τ K) (a : τ → K) (g : MvPolynomial σ F) :
    eval a (aeval s g) = aeval (fun i => eval a (s i)) g := by
  induction g using MvPolynomial.induction_on with
  | C r => simp
  | add p q hp hq => simp [hp, hq]
  | mul_X p i hp => simp [hp]

theorem ThroughPointIncIdeal.eval_genSubst_vanish {K : Type*} [Field K] {n k : ℕ} (x c : Fin n → K)
    (hc : ∑ j, c j * x j = 1) (a : Fin k × Fin n → K) (i : Fin k) :
    ∑ j, eval a (genSubst (k := k) x c (i, j)) * x j = 0 := by
  have h : ∀ j, eval a (genSubst (k := k) x c (i, j)) =
      a (i, j) - (∑ l, a (i, l) * x l) * c j := fun j => by simp [genSubst]
  simp_rw [h, sub_mul, Finset.sum_sub_distrib, mul_assoc, ← Finset.mul_sum, hc, mul_one, sub_self]

theorem ThroughPointIncIdeal.proof : ThroughPointIncIdeal.Statement := by
  intro F _ n k Q x c hc hinc g hg
  apply MvPolynomial.funext
  intro a
  rw [map_zero, ThroughPointIncIdeal.eval_aeval]
  have hu := hinc (fun ij => eval a (genSubst (k := k) x c ij))
    (ThroughPointIncIdeal.eval_genSubst_vanish x c hc a)
  simp only [incIdeal, Submodule.mem_iInf, RingHom.mem_ker] at hg
  exact hg _ hu

end

end GroundTheory.Heights₂.Heights
