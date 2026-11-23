import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.OddDualWeylJacobian.JacRev
import Lemmata.GeneralBFactRightAlt.Imports

open MvPolynomial Matrix

noncomputable section

namespace PI.OddDualWeyl.Uniq

theorem aeval_smul_hom {K S : Type*} [CommRing K] [CommRing S] [Algebra K S] {ι : Type*} [Fintype ι]
    {G : MvPolynomial ι K} {d : ℕ} (hG : IsHomogeneous G d) (c : S) (f : ι → S) :
    aeval (fun v => c * f v) G = c ^ d * aeval f G := by
  first | exact Bl.general_b_fact_right_alt.goal1 .. | (apply Bl.general_b_fact_right_alt.goal1 <;> assumption) | (intros; apply Bl.general_b_fact_right_alt.goal1 <;> assumption)

def P (Rg : Type*) [CommRing Rg] (k : ℕ) : Matrix (Fin k) (Fin k) Rg :=
  Matrix.of fun i j => if i = Fin.rev j then 1 else 0

variable {Rg : Type*} [CommRing Rg] {k : ℕ}

theorem mul_P (B : Matrix (Fin k) (Fin k) Rg) : B * P Rg k = Matrix.of fun i j => B i (Fin.rev j) := by
  ext i j; simp [P, Matrix.mul_apply]

theorem P_transpose : (P Rg k)ᵀ = P Rg k := by
  ext i j
  simp only [P, Matrix.transpose_apply, Matrix.of_apply]
  congr 1
  exact propext ⟨fun h => by rw [h, Fin.rev_rev], fun h => by rw [h, Fin.rev_rev]⟩

theorem P_mul_P : P Rg k * P Rg k = 1 := by
  rw [mul_P]; ext i j; simp [P, Matrix.one_apply]

theorem dualM_eq : dualM Rg k = (adjugate (genM Rg k))ᵀ * P _ k := by
  rw [mul_P]; ext i j; simp [dualM]

theorem map_genM : (dualSub Rg k).toRingHom.mapMatrix (genM Rg k) = dualM Rg k := by
  ext i j; simp [genM, dualSub]

theorem dualSub_dualM (hk : k ≠ 1) (i j : Fin k) :
    dualSub Rg k (dualM Rg k i j) = (P _ k).det * (genM Rg k).det ^ (k - 2) * X (i, j) := by
  have h1 : dualSub Rg k (dualM Rg k i j) = adjugate (dualM Rg k) (Fin.rev j) i := by
    have e : (dualSub Rg k).toRingHom.mapMatrix (adjugate (genM Rg k)) (Fin.rev j) i =
        adjugate (dualM Rg k) (Fin.rev j) i := by
      rw [RingHom.map_adjugate, map_genM]
    rw [← e]; rfl
  have h2 : (adjugate (dualM Rg k))ᵀ * P _ k = ((P _ k).det * (genM Rg k).det ^ (k - 2)) • genM Rg k := by
    rw [dualM_eq, adjugate_mul_distrib, ← adjugate_transpose, adjugate_adjugate _ (by simpa using hk),
      Matrix.transpose_mul, Matrix.transpose_transpose, adjugate_transpose, P_transpose,
      Matrix.mul_assoc, adjugate_mul, Matrix.mul_smul, Matrix.mul_one, smul_smul, Fintype.card_fin]
  have h3 := congrArg (fun M => M i j) h2
  simp only [mul_P, Matrix.of_apply, Matrix.transpose_apply, Matrix.smul_apply, smul_eq_mul] at h3
  rw [h1, h3]; simp [genM]

theorem det_P_ne : (P Rg k).det * (P Rg k).det = 1 := by
  rw [← det_mul, P_mul_P, det_one]

end Uniq

open Uniq in
theorem highest_weight_vector_unique : Uniq := by
  intro K _ k d G hG h0
  by_cases hk : k = 1
  · subst hk
    have hD : ∀ v : Fin 1 × Fin 1, dualM K 1 v.1 v.2 = 1 := by
      intro v; simp only [dualM, adjugate_fin_one, Matrix.of_apply]
      rw [Subsingleton.elim v.2.rev v.1, Matrix.one_apply_eq]
    have hS : dualSub K 1 G = aeval (fun _ => (1 : MvPolynomial (Fin 1 × Fin 1) K)) G := by
      simp only [dualSub, hD]
    have e : G = aeval (fun v : Fin 1 × Fin 1 => X (0, 0) * (1 : MvPolynomial (Fin 1 × Fin 1) K)) G := by
      conv_lhs => rw [← aeval_X_left_apply G]
      exact congrArg (fun f => aeval f G) (funext fun v => by rw [mul_one, Subsingleton.elim v (0, 0)])
    rw [e, aeval_smul_hom hG, ← hS, h0, mul_zero]
  · set c : MvPolynomial (Fin k × Fin k) K := (P _ k).det * (genM K k).det ^ (k - 2)
    have hc : c ≠ 0 := by
      refine mul_ne_zero ?_ (pow_ne_zero _ ?_)
      · intro h; have := det_P_ne (Rg := MvPolynomial (Fin k × Fin k) K) (k := k); rw [h, zero_mul] at this
        exact zero_ne_one this
      · exact det_mvPolynomialX_ne_zero (Fin k) K
    have e : dualSub K k (dualSub K k G) = c ^ d * G := by
      have : (dualSub K k).comp (dualSub K k) = aeval fun v => c * X v := by
        rw [dualSub, comp_aeval]; congr 1; funext v
        exact dualSub_dualM hk v.1 v.2
      rw [← AlgHom.comp_apply, this, aeval_smul_hom hG, aeval_X_left_apply]
    rw [h0, map_zero] at e
    exact (mul_eq_zero.mp e.symm).resolve_left (pow_ne_zero _ hc)

end PI.OddDualWeyl
