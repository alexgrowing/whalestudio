import Mathlib
import Formalism.PeriodIntegrals.RowLetter

open MvPolynomial

noncomputable section

namespace PI.RL.W

open PI.RL

def ChainRule : Prop :=
  ∀ (K : Type) [Field K] (m : ℕ) (vec : Bool) (a b : Fin (m + 1)) (P : MvPolynomial (Fin (m + 1)) K),
    RE K (m + 1) a b (theta K m vec P) =
      ∑ c, theta K m vec (pderiv c P) * RE K (m + 1) a b (Nv K m vec c)

def VecX : Prop :=
  ∀ (K : Type) [Field K] (m : ℕ) (a b c : Fin (m + 1)),
    RE K (m + 1) a b (Nv K m true c) = if c = b then Nv K m true a else 0

def KeyCov : Prop :=
  ∀ (K : Type) [Field K] (m : ℕ) (a b c : Fin (m + 1)),
    RE K (m + 1) a b (Nv K m false c) =
      (if a = b then Nv K m false c else 0) - (if a = c then Nv K m false b else 0)

def HdHom : Prop :=
  ∀ (K : Type) [Field K] (k d : ℕ) (P : MvPolynomial (Fin k) K), P ∈ Hd K k d → P.IsHomogeneous d

theorem theta_X (K : Type) [Field K] (m : ℕ) (vec : Bool) (c : Fin (m + 1)) :
    theta K m vec (X c) = Nv K m vec c := by
  simp [theta]

theorem euler_theta (hH : HdHom) (K : Type) [Field K] (m : ℕ) (vec : Bool) (d : ℕ)
    (P : MvPolynomial (Fin (m + 1)) K) (hP : P ∈ Hd K (m + 1) d) :
    ∑ c, theta K m vec (pderiv c P) * Nv K m vec c = (d : K) • theta K m vec P := by
  have h1 := (hH K (m + 1) d P hP).sum_X_mul_pderiv
  have h2 := congrArg (theta K m vec) h1
  simp only [map_sum, map_mul, theta_X, map_nsmul] at h2
  rw [← Nat.cast_smul_eq_nsmul K] at h2
  rw [← h2]
  exact Finset.sum_congr rfl (fun c _ => mul_comm _ _)

theorem rowLetter_of (hC : ChainRule) (hV : VecX) (hK : KeyCov) (hH : HdHom) : PI.RowLetter := by
  intro K _ m vec d a b P hP
  rw [hC K m vec a b P]
  cases vec
  · have hE := euler_theta hH K m false d P hP
    by_cases hab : a = b
    · subst hab
      have hL : ∑ c, theta K m false (pderiv c P) * RE K (m + 1) a a (Nv K m false c) =
          ∑ c, theta K m false (pderiv c P) * Nv K m false c -
            theta K m false (pderiv a P) * Nv K m false a := by
        have hc : ∀ c, RE K (m + 1) a a (Nv K m false c) =
            Nv K m false c - (if a = c then Nv K m false a else 0) := by
          intro c
          rw [hK K m a a c]
          simp
        simp only [hc, mul_sub, Finset.sum_sub_distrib, mul_ite, mul_zero, Finset.sum_ite_eq,
          Finset.mem_univ, if_true]
      rw [hL, hE]
      simp only [TE, Bool.false_eq_true, if_true, if_false, map_sub, map_smul, map_mul, theta_X]
      rw [mul_comm (Nv K m false a)]
    · have hc : ∀ c, RE K (m + 1) a b (Nv K m false c) =
          -(if a = c then Nv K m false b else 0) := by
        intro c
        rw [hK K m a b c]
        simp [hab]
      simp only [hc, mul_neg, mul_ite, mul_zero, Finset.sum_neg_distrib, Finset.sum_ite_eq,
        Finset.mem_univ, if_true]
      simp [TE, hab, theta_X] <;> ring
  · have hc : ∀ c, RE K (m + 1) a b (Nv K m true c) = if c = b then Nv K m true a else 0 :=
      fun c => hV K m a b c
    simp only [hc, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    simp only [TE, if_true, map_mul, theta_X]
    rw [mul_comm]

end PI.RL.W
