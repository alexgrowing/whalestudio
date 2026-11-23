import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutSE2
import Formalism.HermitianCurvature.HermitianCurvatureProofs.PositionInsertionDiagonalCompat
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ScalarCommuteTransposedRMatrixEntry

open Matrix Formalism.FourierDecayAlt.Wd

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutSE

namespace IbTInvPf

variable {K A S : Type} [Field K] [StarRing K] [Ring A] [StarRing A] [Algebra K A] [StarModule K A]
  [Fintype S] [DecidableEq S]

theorem plus_inv (σ : Site A) (hW : YangianSpanCharacter.T.WeylRel σ.p σ.c σ.ci) (Y : K) (hY : star Y = Y) :
    (!![0, -star σ.ci; star σ.c, algebraMap K A (Y + 1) + star σ.p] : M2 A) * (Ts σ Y)ᴴ = 1 := by
  have hs := congrArg star hW.2.2
  simp only [star_mul, star_add] at hs
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Ts, YangianSpanCharacter.T.Tm, Matrix.mul_apply, Fin.sum_univ_two, Matrix.conjTranspose_apply]
  · rw [← star_mul, hW.1, star_one]
  · rw [← algebraMap_star_comm, hY, mul_add, add_mul, add_mul, one_mul, hs, Algebra.commutes]
    abel
  · rw [← star_mul, hW.2.1, star_one]

theorem minus_inv (σ : Site A) (hW : YangianSpanCharacter.T.WeylRel σ.p σ.c σ.ci) (Y : K) :
    (!![0, -σ.ci; σ.c, algebraMap K A (Y - 1) + σ.p] : M2 A) * ((Ts σ Y).map star)ᴴ = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Ts, YangianSpanCharacter.T.Tm, Matrix.mul_apply, Fin.sum_univ_two, Matrix.conjTranspose_apply]
  · exact hW.2.1
  · rw [mul_add, add_mul, sub_mul, one_mul, hW.2.2, Algebra.commutes]
    abel
  · exact hW.1

theorem lift_zero_one : (lift0 (1 : M2 A) : M2 (SlopeTestRemainingChoices S A)) = 1 := by
  unfold lift0
  ext i j
  rw [Matrix.map_apply, Matrix.one_apply, Matrix.one_apply]
  split_ifs <;> simp [io]

theorem ivlet_mul_star (σ : Site A) (hW : YangianSpanCharacter.T.WeylRel σ.p σ.c σ.ci) (l : Letter K S)
    (hl : star l.pt = l.pt) : ivlet σ l * star (vlet σ l) = 1 := by
  unfold ivlet vlet
  rw [Formalism.FourierDecayAlt.P.Wd1.ins_star _ _ (Formalism.FourierDecayAlt.P.Wd7.freeOf2_lift _ _),
    ← Formalism.FourierDecayAlt.P.Wd1.ins_mul _ _ _ (Formalism.FourierDecayAlt.P.Wd7.freeOf2_lift _ _), Formalism.FourierDecayAlt.P.Wd7.liftMatrix_conjTranspose,
    ← Formalism.FourierDecayAlt.P.Wd7.lift_reduction_mul]
  cases hpl : l.plus
  · simp only [Bool.false_eq_true, ite_false]
    rw [minus_inv σ hW l.pt, lift_zero_one, Formalism.FourierDecayAlt.P.Wd1.ins_one]
  · simp only [ite_true]
    rw [plus_inv σ hW l.pt hl, lift_zero_one, Formalism.FourierDecayAlt.P.Wd1.ins_one]

theorem ibT_mul_star (σ : Site A) (hσ : IsSite σ) :
    ∀ w : List (Letter K S), (∀ l ∈ w, star l.pt = l.pt) → ibT σ w * star (bT σ w) = 1
  | [], _ => by simp [ibT, bT]
  | l :: w, h => by
    have hw := ibT_mul_star σ hσ w (fun l' hl' => h l' (List.mem_cons_of_mem _ hl'))
    rw [ibT, bT, star_mul, mul_assoc, ← mul_assoc (ibT σ w), hw, one_mul,
      ivlet_mul_star σ hσ.1 l (h l (by simp))]

end IbTInvPf

theorem boundary_torus_invariance : IbTInv := by
  intro K A S _ _ _ _ _ _ _ _ σ w hσ hw
  exact IbTInvPf.ibT_mul_star σ hσ w hw

end Formalism.FourierDecayAlt.P.CutSE
