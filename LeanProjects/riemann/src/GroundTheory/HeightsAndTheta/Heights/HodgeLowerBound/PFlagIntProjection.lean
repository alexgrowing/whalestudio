import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StatementsFlagIntProjection
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StatementsBlockAltUnique
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StatementsFlagIntMuDegree
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StatementsFlagIntMuProd
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StatementsFlagIntMuOne
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial Equiv

namespace FlagIntProjection

variable (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ)

omit [Fintype Ψ] [DecidableEq Ψ] in
theorem weylAct_comp (v w : Ψ → Perm (Fin N)) : weylAct Ψ N v ∘ weylAct Ψ N w = weylAct Ψ N (v * w) := by
  funext p
  rfl

omit [DecidableEq Ψ] in
theorem weylSign_mul (v w : Ψ → Perm (Fin N)) : weylSign Ψ N (v * w) = weylSign Ψ N v * weylSign Ψ N w := by
  unfold weylSign
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun τ _ => ?_
  rw [Pi.mul_apply, Perm.sign_mul]
  push_cast
  ring

omit [DecidableEq Ψ] in
theorem weylSign_mul_self (w : Ψ → Perm (Fin N)) : weylSign Ψ N w * weylSign Ψ N w = 1 := by
  unfold weylSign
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_eq_one fun τ _ => ?_
  rw [← Int.cast_mul, ← Units.val_mul, Int.units_mul_self]
  simp

theorem flagInt_rename (w : Ψ → Perm (Fin N)) (Q : RootPoly Ψ N) :
    flagInt Ψ N (rename (weylAct Ψ N w) Q) = weylSign Ψ N w * flagInt Ψ N Q := by
  unfold flagInt antisym
  simp_rw [rename_rename, weylAct_comp]
  have hs : ∀ v, weylSign Ψ N v = weylSign Ψ N w * weylSign Ψ N (v * w) := fun v => by
    rw [weylSign_mul, mul_comm (weylSign Ψ N v), ← mul_assoc, weylSign_mul_self, one_mul]
  rw [Finset.sum_congr rfl fun v _ => by rw [hs v, mul_smul], ← Finset.smul_sum, coeff_smul, smul_eq_mul]
  congr 2
  exact Equiv.sum_comp (Equiv.mulRight w) (fun u => weylSign Ψ N u • rename (weylAct Ψ N u) Q)

variable (j : ℕ)

theorem muPoly_rename (w : Ψ → Perm (Fin N)) (hw : IsBlockPerm Ψ N j w) :
    rename (weylAct Ψ N w) (muPoly Ψ N j) = muPoly Ψ N j := by
  unfold muPoly
  rw [map_sum, Finset.sum_filter, Finset.sum_filter]
  simp only [rename_X]
  rw [← (Equiv.prodCongrRight fun τ => w τ).sum_comp
    (fun q => if ¬ (q.2 : ℕ) < j then (X q : RootPoly Ψ N) else 0)]
  refine Finset.sum_congr rfl fun ⟨τ, i⟩ _ => ?_
  simp only [weylAct, Equiv.prodCongrRight_apply, hw τ i]

def flagIntMul (Q : RootPoly Ψ N) : RootPoly Ψ N →ₗ[ℚ] ℚ where
  toFun P := flagInt Ψ N (Q * P)
  map_add' P P' := by
    simp only [flagInt, antisym, mul_add, map_add, smul_add, Finset.sum_add_distrib, coeff_add]
  map_smul' c P := by
    simp only [flagInt, antisym, mul_smul_comm, map_smul, smul_comm _ c, ← Finset.smul_sum, coeff_smul,
      smul_eq_mul, RingHom.id_apply]

end FlagIntProjection

open FlagIntProjection in

theorem FlagIntProjection.proof (hU : BlockAltUnique.Statement) (hD : FlagIntMuDegree.Statement)
    (hP : FlagIntMuProd.Statement) (hO : FlagIntMuOne.Statement) : FlagIntProjection.Statement := by
  intro Ψ _ _ N j hj P
  have key := hU Ψ N j hj (flagIntMul Ψ N (muPoly Ψ N j ^ dimN Ψ N j))
    (fun w hw P => by
      show flagInt Ψ N (_ * rename _ P) = _ * flagInt Ψ N (_ * P)
      have h : muPoly Ψ N j ^ dimN Ψ N j * rename (weylAct Ψ N w) P =
          rename (weylAct Ψ N w) (muPoly Ψ N j ^ dimN Ψ N j * P) := by
        rw [map_mul, map_pow, muPoly_rename Ψ N j w hw]
      rw [h, flagInt_rename])
    (fun b hb => hD Ψ N j hj b hb) P
  change flagInt Ψ N (_ * P) = flagInt Ψ N (_ * monomial _ 1) * blockInt Ψ N j P at key
  rw [key, hP Ψ N j hj, hO N j hj]
  unfold grassProdDeg dimN
  rw [mul_pow, ← pow_mul]
  ring_nf

end GroundTheory.Heights₂.Heights.LowerBoundFree
