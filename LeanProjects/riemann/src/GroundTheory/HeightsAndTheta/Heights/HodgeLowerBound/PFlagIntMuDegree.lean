import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.FrameDefinitions.PermFinTwoUniv
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StatementsFlagIntMuDegree
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial

namespace FlagIntMuDegree

variable (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ)

omit [DecidableEq Ψ] in

theorem muPoly_isHomogeneous (j : ℕ) : (muPoly Ψ N j).IsHomogeneous 1 :=
  IsHomogeneous.sum _ _ _ fun p _ => isHomogeneous_X ℚ p

theorem antisym_isHomogeneous {P : RootPoly Ψ N} {m : ℕ} (hP : P.IsHomogeneous m) :
    (antisym Ψ N P).IsHomogeneous m :=
  IsHomogeneous.sum _ _ _ fun w _ =>
    (homogeneousSubmodule (Ψ × Fin N) ℚ m).smul_mem (weylSign Ψ N w) hP.rename_isHomogeneous

omit [DecidableEq Ψ] in

theorem sum_fin_ite (j : ℕ) (hj : j ≤ N) :
    (∑ i : Fin N, if (i : ℕ) < j then N - j else 0) = j * (N - j) := by
  rw [Fin.sum_univ_eq_sum_range (fun i => if i < j then N - j else 0) N, ← Finset.sum_filter,
    show (Finset.range N).filter (· < j) = Finset.range j by
      ext i; simp only [Finset.mem_filter, Finset.mem_range]; omega,
    Finset.sum_const, Finset.card_range, smul_eq_mul]

omit [DecidableEq Ψ] in

theorem rhoMono_degree (j : ℕ) (hj : j ≤ N) :
    (rhoMono Ψ N).degree = dimN Ψ N j + (rhoBlock Ψ N j).degree := by
  simp only [Finsupp.degree_eq_sum, rhoMono, rhoBlock, Finsupp.coe_equivFunOnFinite_symm, dimN]
  have hpt : ∀ p : Ψ × Fin N, N - 1 - (p.2 : ℕ) =
      (if (p.2 : ℕ) < j then N - j else 0) +
        (if (p.2 : ℕ) < j then j - 1 - (p.2 : ℕ) else N - 1 - (p.2 : ℕ)) := by
    intro p
    have := p.2.isLt
    split_ifs <;> omega
  rw [Finset.sum_congr rfl fun p _ => hpt p, Finset.sum_add_distrib]
  congr 1
  rw [Fintype.sum_prod_type]
  simp only [sum_fin_ite N j hj, Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_assoc]

theorem proof : FlagIntMuDegree.Statement := by
  intro Ψ _ _ N j hj b hb
  have hP : (muPoly Ψ N j ^ dimN Ψ N j * monomial b (1 : ℚ)).IsHomogeneous
      (dimN Ψ N j + b.degree) := by
    have h := ((muPoly_isHomogeneous Ψ N j).pow (dimN Ψ N j)).mul
      (isHomogeneous_monomial (1 : ℚ) (rfl : b.degree = b.degree))
    rwa [one_mul] at h
  unfold flagInt
  refine (antisym_isHomogeneous Ψ N hP).coeff_eq_zero ?_
  rw [rhoMono_degree Ψ N j hj]
  omega

end FlagIntMuDegree

end GroundTheory.Heights₂.Heights.LowerBoundFree
